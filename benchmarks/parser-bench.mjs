#!/usr/bin/env node
// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Parser benchmark.
//
// The only end-to-end pipeline that ships today is parse + check on .twasm
// source — Idris2 proofs are static, Zig FFI runs out-of-process, and the
// post-codegen Rust verifier consumes wasm, not .twasm. So the parser is
// where benchmark evidence has to live until L1-L6 codegen exists.
//
// Per-example wallclock measurements with the warm-up + repeat-N pattern
// the maintenance standard expects (`.machine_readable/policies/
// MAINTENANCE-AXES.a2ml` axis-3 effects-evidence). Reports median + p95 +
// min + throughput (KB/s of source parsed-and-checked) per example, plus
// an aggregate roll-up. Skips examples that the parser rejects with a
// reason (L11/L12 grammar not in the v1.5 parser).
//
// Output:
//   - Human-readable table on stdout
//   - JSON summary on stderr (machine-readable for trend tracking)
//
// Invocation:
//   node benchmarks/parser-bench.mjs                 # default: 200 iters
//   BENCH_ITERS=1000 node benchmarks/parser-bench.mjs
//   BENCH_FORMAT=json node benchmarks/parser-bench.mjs > metrics.json

import { readFileSync, readdirSync } from "node:fs";
import { resolve, dirname, basename } from "node:path";
import { fileURLToPath } from "node:url";
import { parseModule } from "../src/parser/Parser.mjs";
import { checkModule } from "../src/parser/Checker.mjs";

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, "..");
const EXAMPLES = resolve(ROOT, "examples");

const ITERS = Number(process.env.BENCH_ITERS ?? 200);
const WARMUP = Math.max(10, Math.floor(ITERS / 10));
const FORMAT = process.env.BENCH_FORMAT ?? "human"; // human | json

// ─────────────────────────────────────────────────────────────────────────
// Stats helpers
// ─────────────────────────────────────────────────────────────────────────

function quantile(sorted, q) {
  if (sorted.length === 0) return NaN;
  const idx = Math.min(sorted.length - 1, Math.floor(q * sorted.length));
  return sorted[idx];
}

function summarise(samplesMs, bytes) {
  const sorted = [...samplesMs].sort((a, b) => a - b);
  const median = quantile(sorted, 0.5);
  const p95 = quantile(sorted, 0.95);
  const min = sorted[0];
  const max = sorted[sorted.length - 1];
  const mean = samplesMs.reduce((a, b) => a + b, 0) / samplesMs.length;
  // Throughput from the median: kilobytes parsed-and-checked per second.
  const throughput_kBs = median > 0 ? (bytes / 1024) / (median / 1000) : Infinity;
  return { median_ms: median, p95_ms: p95, min_ms: min, max_ms: max, mean_ms: mean, throughput_kBs };
}

function fmtMs(x) {
  if (!Number.isFinite(x)) return "n/a";
  if (x < 1) return `${(x * 1000).toFixed(0)}µs`;
  return `${x.toFixed(2)}ms`;
}
function fmtKBs(x) {
  if (!Number.isFinite(x)) return "n/a";
  if (x >= 1024) return `${(x / 1024).toFixed(2)}MB/s`;
  return `${x.toFixed(0)}kB/s`;
}

// ─────────────────────────────────────────────────────────────────────────
// Pragma extraction (mirrors e2e-driver: skip examples whose grammar isn't
// in the v1.5 parser, so the benchmark doesn't measure "parser fails fast")
// ─────────────────────────────────────────────────────────────────────────

function shouldSkip(source) {
  for (const line of source.split("\n")) {
    const m = line.match(/\/\/\s*E2E:\s*skip(?:\s+(.+))?/);
    if (m) return m[1] ?? "(no reason)";
  }
  return null;
}

// ─────────────────────────────────────────────────────────────────────────
// One-shot timing
// ─────────────────────────────────────────────────────────────────────────

function timeOne(source) {
  const t0 = process.hrtime.bigint();
  const r = parseModule(source);
  if (r.TAG !== "Ok") {
    const t1 = process.hrtime.bigint();
    return { ok: false, ms: Number(t1 - t0) / 1e6, reason: `parse failed: ${r._0.message}` };
  }
  checkModule(r._0);
  const t1 = process.hrtime.bigint();
  return { ok: true, ms: Number(t1 - t0) / 1e6 };
}

// ─────────────────────────────────────────────────────────────────────────
// Per-example benchmark
// ─────────────────────────────────────────────────────────────────────────

function benchExample(filename) {
  const path = resolve(EXAMPLES, filename);
  const source = readFileSync(path, "utf-8");
  const bytes = Buffer.byteLength(source, "utf8");

  const skipReason = shouldSkip(source);
  if (skipReason) {
    return { filename, bytes, status: "skip", reason: skipReason };
  }

  // Warm-up: JIT primes V8's optimiser; throws away samples to avoid
  // pulling the median toward cold-cache cost.
  for (let i = 0; i < WARMUP; i++) {
    const r = timeOne(source);
    if (!r.ok) return { filename, bytes, status: "fail", reason: r.reason };
  }

  const samples = [];
  for (let i = 0; i < ITERS; i++) {
    const r = timeOne(source);
    if (!r.ok) return { filename, bytes, status: "fail", reason: r.reason };
    samples.push(r.ms);
  }
  return { filename, bytes, status: "ok", ...summarise(samples, bytes) };
}

// ─────────────────────────────────────────────────────────────────────────
// Run
// ─────────────────────────────────────────────────────────────────────────

const exampleFiles = readdirSync(EXAMPLES).filter((f) => f.endsWith(".twasm")).sort();

if (exampleFiles.length === 0) {
  console.error("No examples/*.twasm found — nothing to benchmark");
  process.exit(1);
}

if (FORMAT === "human") {
  console.log(`typed-wasm parser benchmark`);
  console.log(`  examples : ${exampleFiles.length}`);
  console.log(`  iters    : ${ITERS} (warmup ${WARMUP})`);
  console.log(`  node     : ${process.version}`);
  console.log("");
  console.log(
    `  ${"example".padEnd(36)} ${"bytes".padStart(7)} ${"median".padStart(10)} ${"p95".padStart(10)} ${"min".padStart(10)} ${"throughput".padStart(11)}`,
  );
  console.log(`  ${"-".repeat(36)} ${"-".repeat(7)} ${"-".repeat(10)} ${"-".repeat(10)} ${"-".repeat(10)} ${"-".repeat(11)}`);
}

const results = [];
let totalBytes = 0;
let totalMedianMs = 0;
let okCount = 0;
let failCount = 0;
let skipCount = 0;

for (const f of exampleFiles) {
  const r = benchExample(f);
  results.push(r);
  if (r.status === "ok") {
    okCount++;
    totalBytes += r.bytes;
    totalMedianMs += r.median_ms;
    if (FORMAT === "human") {
      console.log(
        `  ${basename(f).padEnd(36)} ${String(r.bytes).padStart(7)} ${fmtMs(r.median_ms).padStart(10)} ${fmtMs(r.p95_ms).padStart(10)} ${fmtMs(r.min_ms).padStart(10)} ${fmtKBs(r.throughput_kBs).padStart(11)}`,
      );
    }
  } else if (r.status === "skip") {
    skipCount++;
    if (FORMAT === "human") {
      console.log(`  ${basename(f).padEnd(36)} ${String(r.bytes).padStart(7)} ${"SKIP".padStart(10)} (${r.reason})`);
    }
  } else {
    failCount++;
    if (FORMAT === "human") {
      console.log(`  ${basename(f).padEnd(36)} ${String(r.bytes).padStart(7)} ${"FAIL".padStart(10)} (${r.reason})`);
    }
  }
}

const aggregateThroughput =
  totalMedianMs > 0 ? (totalBytes / 1024) / (totalMedianMs / 1000) : Infinity;

if (FORMAT === "human") {
  console.log("");
  console.log(`  Aggregate: ${okCount} ok, ${skipCount} skip, ${failCount} fail`);
  console.log(`  Total bytes parsed-and-checked: ${totalBytes}`);
  console.log(`  Sum of medians: ${fmtMs(totalMedianMs)}`);
  console.log(`  Aggregate throughput: ${fmtKBs(aggregateThroughput)}`);
}

// JSON summary always to stderr so `BENCH_FORMAT=json node parser-bench.mjs`
// can redirect stdout to a metrics file while still keeping stderr human.
const summary = {
  schema: "typed-wasm/parser-bench/1",
  iters: ITERS,
  warmup: WARMUP,
  node_version: process.version,
  examples: results,
  aggregate: {
    ok: okCount,
    skip: skipCount,
    fail: failCount,
    total_bytes: totalBytes,
    sum_median_ms: totalMedianMs,
    throughput_kBs: aggregateThroughput,
  },
};

if (FORMAT === "json") {
  process.stdout.write(JSON.stringify(summary, null, 2) + "\n");
} else {
  process.stderr.write(JSON.stringify(summary) + "\n");
}

process.exit(failCount > 0 ? 1 : 0);
