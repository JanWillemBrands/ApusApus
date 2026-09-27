#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
FUZZER="$ROOT/SwiftSyntaxFuzzer"
BUILD="$FUZZER/.build"
# Xcode's DerivedData and package checkouts live OUTSIDE the repository. In ApusApus the
# SwiftSyntaxFuzzer folder is part of the Xcode project, so checkouts under `$BUILD` would be seen
# as project folders too ("already open as a Folder", duplicate nested packages) and package
# resolution fails.
XCODE_CACHE="${HOME}/Library/Caches/ApusApusFuzzer"
XCODE_DERIVED_DATA="${ADVENT_FUZZER_DERIVED_DATA:-$XCODE_CACHE/DerivedData}"
XCODE_SOURCE_PACKAGES="${ADVENT_FUZZER_SOURCE_PACKAGES:-$XCODE_CACHE/SourcePackages}"
XCODE_LOG="${ADVENT_FUZZER_XCODE_LOG:-/tmp/advent-fuzzer-xcodebuild.log}"

mkdir -p "$BUILD"
mkdir -p "$BUILD/module-cache"

if [[ "${ADVENT_FUZZER_SKIP_XCODEBUILD:-0}" != "1" ]]; then
  echo "Building ApusApus dependencies with Xcode..."
  xcodebuild \
    -project "$ROOT/ApusApus.xcodeproj" \
    -scheme ApusApus \
    -configuration Release \
    -destination 'platform=macOS,arch=arm64' \
    -derivedDataPath "$XCODE_DERIVED_DATA" \
    -clonedSourcePackagesDirPath "$XCODE_SOURCE_PACKAGES" \
    build >"$XCODE_LOG"
else
  echo "Skipping Xcode build because ADVENT_FUZZER_SKIP_XCODEBUILD=1"
fi

# Only what the probe and the ApusApus sources import (SwiftParser, SwiftSyntax and its
# versioned modules, BitCollections), which is what the ApusApus app target links.
required_object_names=(
  BitCollections.o
  InternalCollectionsUtilities.o
  SwiftParser.o
  SwiftSyntax.o
  SwiftSyntax509.o
  SwiftSyntax510.o
  SwiftSyntax600.o
  SwiftSyntax601.o
  SwiftSyntax602.o
  SwiftSyntax603.o
  SwiftSyntax604.o
  _SwiftSyntaxCShims.o
)

contains_required_objects() {
  local dir="$1"
  [[ -d "$dir" ]] || return 1
  local object
  for object in "${required_object_names[@]}"; do
    [[ -f "$dir/$object" ]] || return 1
  done
}

derived_data_root_for_products() {
  local products="$1"
  (cd "$products/../../.." && pwd)
}

discover_products_dir() {
  local candidates=()

  if [[ -n "${ADVENT_FUZZER_PRODUCTS:-}" ]]; then
    candidates+=("$ADVENT_FUZZER_PRODUCTS")
  fi

  candidates+=("$XCODE_DERIVED_DATA/Build/Products/Release")

  if [[ -d "$HOME/Library/Developer/Xcode/DerivedData" ]]; then
    while IFS= read -r candidate; do
      candidates+=("$candidate")
    done < <(
      find "$HOME/Library/Developer/Xcode/DerivedData" \
        -path '*/Build/Products/Release/SwiftSyntax.o' \
        -print 2>/dev/null \
        | sed 's#/SwiftSyntax\.o$##' \
        | sort -r
    )
  fi

  local candidate
  for candidate in "${candidates[@]}"; do
    if contains_required_objects "$candidate"; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done

  return 1
}

PRODUCTS="$(discover_products_dir || true)"
if [[ -z "$PRODUCTS" ]]; then
  cat >&2 <<EOF
Could not find ApusApus Release build products with the SwiftSyntax object files.

Try one of these:
  1. Run SwiftSyntaxFuzzer/bin/build.sh without ADVENT_FUZZER_SKIP_XCODEBUILD=1.
  2. Build the ApusApus scheme in Xcode, then rerun with ADVENT_FUZZER_SKIP_XCODEBUILD=1.
  3. Set ADVENT_FUZZER_PRODUCTS=/path/to/Build/Products/Release.

Xcode build log, if attempted: $XCODE_LOG
EOF
  exit 1
fi

DERIVED_DATA_ROOT="$(derived_data_root_for_products "$PRODUCTS")"
SHIMS_SUBPATH="checkouts/swift-syntax/Sources/_SwiftSyntaxCShims/include"
# Checkouts made by this script live in $XCODE_SOURCE_PACKAGES; products found elsewhere (plain
# Xcode DerivedData) keep theirs next to the products.
if [[ -d "$XCODE_SOURCE_PACKAGES/$SHIMS_SUBPATH" ]]; then
  DEFAULT_SHIMS="$XCODE_SOURCE_PACKAGES/$SHIMS_SUBPATH"
else
  DEFAULT_SHIMS="$DERIVED_DATA_ROOT/SourcePackages/$SHIMS_SUBPATH"
fi
SWIFT_SYNTAX_SHIMS="${ADVENT_FUZZER_SWIFT_SYNTAX_SHIMS:-$DEFAULT_SHIMS}"

if [[ ! -d "$SWIFT_SYNTAX_SHIMS" ]]; then
  cat >&2 <<EOF
Could not find _SwiftSyntaxCShims include directory:
  $SWIFT_SYNTAX_SHIMS

Set ADVENT_FUZZER_SWIFT_SYNTAX_SHIMS=/path/to/swift-syntax/Sources/_SwiftSyntaxCShims/include.
EOF
  exit 1
fi

echo "Using Xcode products: $PRODUCTS"
echo "Using SwiftSyntax shims: $SWIFT_SYNTAX_SHIMS"

ADVENT_SOURCES=()
while IFS= read -r source; do
  ADVENT_SOURCES+=("$source")
done < <(
  find "$ROOT/ApusApus" -maxdepth 1 -name '*.swift' \
    ! -name 'main.swift' \
    ! -name 'bench_identifier.swift' \
    | sort
)

DEPENDENCY_OBJECTS=()
for object in "${required_object_names[@]}"; do
  DEPENDENCY_OBJECTS+=("$PRODUCTS/$object")
done

echo "Building fuzzer probe..."
xcrun swiftc \
  -swift-version 5 \
  -O \
  -enable-bare-slash-regex \
  -module-cache-path "$BUILD/module-cache" \
  -I "$PRODUCTS" \
  -I "$SWIFT_SYNTAX_SHIMS" \
  "${ADVENT_SOURCES[@]}" \
  "$FUZZER/Sources/AdventProbe/ProbeMain.swift" \
  "${DEPENDENCY_OBJECTS[@]}" \
  -o "$BUILD/advent-fuzz-probe"

echo "Building fuzzer runner..."
xcrun swiftc \
  -swift-version 5 \
  -O \
  -parse-as-library \
  -module-cache-path "$BUILD/module-cache" \
  "$FUZZER/Sources/AdventFuzzRunner/main.swift" \
  -o "$BUILD/advent-fuzz-runner"

echo "Built:"
echo "  $BUILD/advent-fuzz-probe"
echo "  $BUILD/advent-fuzz-runner"
