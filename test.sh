#!/bin/zsh

THIS_DIR=${0:A:h}
CONF_FILE=$THIS_DIR/configuration.sh

source $CONF_FILE

zparseopts -D -E -- u=UNIT -unit=UNIT

function blue()  { print -P "%F{blue}%B$1%b%f" }
function green() { print -P "%F{green}%B$1%b%f" }
function red()   { print -P "%F{red}%B$1%b%f" }

typeset -A TESTS
TESTS=( "01. stall hand"    "-M stalling_cpu  $THIS_DIR/examples/verilog/stall.v" \
        "02. mips fragment" "-M mips_pipeline $IVL_DIR/benchmarks/472-mips-pipelined/472-mips-fragment.v" \
      )

echo

TEST_PL="$THIS_DIR/src/test/unittest.pl"

blue "================================================================================"
blue "   RUNNING UNIT TESTS"
blue "================================================================================"

sicstus \
    -f --nologo --noinfo \
    -l "$TEST_PL" \
    --goal "(unit_test, halt) ; halt(1)." 2>&1 | \
    awk ' /^%/ {print $0;} /^[^%]/ { printf("[1;31m%s[1;0m\n", $0); } /tests? failed/ {failed = 1;} END {if(failed) {exit 1;} else {exit 0;}}'

last_err=$?

if [[ $last_err -ne 0 ]]; then
    echo
    red "================================================================================"
    red "   UNIT TESTS FAILED !" 1>&2
    red "================================================================================"
    exit 1
fi

if [[ -z "$UNIT" ]]; then
    for test_name in ${(ok)TESTS}; do
        blue "================================================================================"
        blue "   RUNNING $test_name"
        blue "================================================================================"

        test_input="${TESTS[$test_name]}"
        local -a test_arr
        test_arr=("${(@s/ /)test_input}")
        
        if ! $THIS_DIR/verylog ${test_arr}; then
            echo
            red "================================================================================"
            red "   TEST '$test_name' FAILED !" 1>&2
            red "================================================================================"
            exit 1
        else
            echo "\n"
        fi
    done
fi

green "================================================================================"
green "   ALL TESTS PASSED !"
green "================================================================================"
