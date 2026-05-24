#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# git-cleanup.sh — Repository hygiene script
set -euo pipefail
echo "Cleaning up merged branches..."
git fetch -p
git branch --merged | grep -v "\*" | grep -v "main" | xargs -n 1 git branch -d || echo "No branches to clean."
echo "Pruning remote tracking branches..."
git remote prune origin
