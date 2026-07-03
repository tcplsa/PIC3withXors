#!/bin/bash
# Build script for PDR BLIF SAT solver dependencies
# Run in blif/ directory:  bash build.sh

set -e
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

echo "=== Building SAT solver dependencies ==="

# 1. Build MiniSat
echo ""
echo "--- Building MiniSat ---"
if [ -d minisat/minisat ]; then
    cd minisat
    make clean 2>/dev/null || true
    make -j$(nproc) r lr
    cd "$SCRIPT_DIR"
    echo "MiniSat built: $(ls minisat/build/dynamic/lib/libminisat.so 2>/dev/null || echo 'check build output')"
else
    echo "ERROR: minisat/minisat/ source not found!"
    echo "  Clone: git clone https://github.com/niklasso/minisat.git minisat/minisat"
    exit 1
fi

# 2. Build CryptoMiniSat5
echo ""
echo "--- Building CryptoMiniSat5 ---"
if [ -d cryptominisat/src ]; then
    cd cryptominisat
    mkdir -p build
    cd build
    cmake .. -DCMAKE_BUILD_TYPE=Release -DSTATICCOMPILE=ON
    make -j$(nproc)
    cd "$SCRIPT_DIR"
    echo "CryptoMiniSat built: $(ls cryptominisat/build/lib/libcryptominisat5.so 2>/dev/null)"
else
    echo "WARNING: cryptominisat/src/ not found, skipping CryptoMiniSat"
    echo "  (MiniSat will be used as fallback)"
fi

# 3. Compile MiniSat C wrapper
echo ""
echo "--- Compiling MiniSat wrapper ---"
if [ -f minisat_c_wrapper.cpp ]; then
    g++ -std=c++11 -shared -fPIC -O3 \
        -o libminisat_wrapper.so \
        minisat_c_wrapper.cpp \
        -I minisat -I minisat/minisat \
        -L minisat/build/dynamic/lib -lminisat \
        -Wl,-rpath,'$ORIGIN'/minisat/build/dynamic/lib
    echo "libminisat_wrapper.so built"
else
    echo "ERROR: minisat_c_wrapper.cpp not found!"
    exit 1
fi

# 4. Compile CryptoMiniSat C wrapper
echo ""
echo "--- Compiling CryptoMiniSat wrapper ---"
if [ -f cmsat_wrapper.cpp ] && [ -f cryptominisat/build/lib/libcryptominisat5.so ]; then
    g++ -std=c++11 -shared -fPIC -O3 \
        -o libcmsat_wrapper.so \
        cmsat_wrapper.cpp \
        -I cryptominisat/build/include/cryptominisat5 \
        -L cryptominisat/build/lib -lcryptominisat5 \
        -Wl,-rpath,'$ORIGIN'/cryptominisat/build/lib
    echo "libcmsat_wrapper.so built"
else
    echo "Skipping CryptoMiniSat wrapper (missing source or lib)"
fi

echo ""
echo "=== Build complete ==="
echo "Library files:"
ls -la lib*.so 2>/dev/null
echo ""
echo "To test: python mainblif.py <file.blif>"
