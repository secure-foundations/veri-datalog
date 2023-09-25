#!/bin/bash

set -euxo pipefail

# Bottom up.
(
    cd ../bottom-up
    make clean all check
)

# Top down.
(
    cd ../top-down
    make clean test-no-verify
)
