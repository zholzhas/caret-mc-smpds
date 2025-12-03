zig build --release=safe
echo "SMPDS"
./zig-out/bin/caret_mc_smpds ./tests/perftest.json -pytest
echo "PDS"
./zig-out/bin/caret_mc_smpds ./tests/perftest.json -pytest -naive