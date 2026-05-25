# Wiki source

These markdown files mirror the project's GitHub wiki at
https://github.com/hyperpolymath/typed-wasm/wiki.

The wiki lives in a separate git repo (`typed-wasm.wiki.git`) that
isn't directly writable from sandboxed sessions in this workspace —
the commit-signing infrastructure is scoped to `typed-wasm.git`. So
the source of truth for wiki content lives here in `docs/wiki/`,
committed alongside the code, and gets sync'd to the wiki repo by the
maintainer.

## Sync workflow

```bash
# One-time setup
git clone https://github.com/hyperpolymath/typed-wasm.wiki.git ~/twasm-wiki

# After updating docs/wiki/ files in this repo:
cp docs/wiki/*.md ~/twasm-wiki/
cd ~/twasm-wiki
git add -A
git commit -m "Sync from typed-wasm docs/wiki/"
git push
```

## Page inventory

| Page | Purpose |
|---|---|
| `Home.md` | Wiki landing page; current state + links to other pages |
| `Production-Path.md` | The 6-phase production plan (companion to `docs/PRODUCTION-PATH.adoc`) |
| `Phase-0-Status.md` | Live closure state with PR cross-links + test surface summary |
| `Comparison.md` | Landscape of typed-wasm vs neighbouring approaches at each maturity level |

## Authoring rules

- Markdown (GitHub-flavoured) — wiki engine renders MD, not AsciiDoc
- All cross-references between wiki pages use `[Page Name](Page-Name)` syntax (no `.md` extension on the link)
- Repo-internal references use absolute URLs:
  `https://github.com/hyperpolymath/typed-wasm/blob/main/<path>`
- Keep pages oriented around outside-reader discovery, not maintainer
  reference (the `docs/` directory is the maintainer reference)
- When the canonical statement lives in a repo doc (e.g.
  `docs/PRODUCTION-PATH.adoc`), the wiki page summarises and links
  rather than duplicating
