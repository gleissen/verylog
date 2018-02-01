# verylog

## Instructions

First copy the `configuration-skeleton.sh` file into `configuration.sh`, and
fill the missing parts.

## Command Line Options

``` sh
run [parser options] <verilog file>

parser options:
  -M <toplevel module name>
      When the verilog file contains multiple modules, this is used to denote the toplevel one
```

### Example

```sh
./run -M stalling_cpu examples/verilog/stall.v
```
