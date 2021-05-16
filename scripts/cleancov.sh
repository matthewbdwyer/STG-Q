#!/usr/bin/env bash
# declare -r ROOT_DIR=${$STGQ_HOME:-$(git rev-parse --show-toplevel)}

find $STGQ_HOME -name '*gcda' -delete