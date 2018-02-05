#!/bin/zsh

THIS_DIR=${0:A:h}
CONF_FILE=$THIS_DIR/configuration.sh

source $CONF_FILE

typeset -A TESTS
TESTS=( "01: stall hand"    "-M stalling_cpu  $THIS_DIR/examples/verilog/stall.v" \
        "02: mips fragment" "-M mips_pipeline $IVL_DIR/benchmarks/472-mips-pipelined/472-mips-fragment.v" \
      )

echo

for test_name in ${(k)TESTS}; do
    echo "================================================================================"
    echo "   RUNNING $test_name"
    echo "================================================================================"

    test_input="${TESTS[$test_name]}"
    local -a test_arr
    test_arr=("${(@s/ /)test_input}")
    
    if ! $THIS_DIR/verylog ${test_arr}; then
        echo "TEST '$test_name' FAILED !" 1>&2
        exit 1
    else
        echo "\n"
    fi
done

echo "================================================================================"
echo "   ALL TESTS PASSED"
echo "================================================================================"
