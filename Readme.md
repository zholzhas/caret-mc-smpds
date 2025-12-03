# Tool for CARET model checking Self-Modifying Pushdown Systems

This is the implementation of the model checking algorithm presented
in the paper: Touili, Tayssir and Zhangeldinov, Olzhas (2025) "CARET Model Checking of Self Modifying Code."

## Usage
1. Build the binary
```
zig build install [release=safe|release=fast|release=small]
```
The binary will be compiled into zig-out/bin/caret_mc_smpds.

2. Execute
```
./zig-out/bin/caret_mc_smpds [-bin] [filename]
```
The program will return True if the file contains a model that satsifies the CARET formula (the formula also should be in the file).

The tool accepts a configuration of an SM-PDS either in a human readable .smpds format, or
in a machine readable .json format (see folder examples/ for format examples and parser.zig for exact parsing algorithms).
For .json files, use the -bin option.
