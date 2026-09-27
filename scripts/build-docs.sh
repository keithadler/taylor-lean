#!/bin/sh
# Refresh the browser version in docs/: the widget's JavaScript and the props Lean computes.
set -e
cd "$(dirname "$0")/.."
lake build
cp widget/Taylor.js docs/Taylor.js
lake env lean --run scripts/Props.lean
