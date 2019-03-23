#!/bin/bash
set -e
cd Code
# rm *.ibc
for file in *.idr
do
  echo "checking $file"
  time idris --check --package contrib "$file"
  echo "---------------------------------------------------------------------------------"
  echo ""
done
