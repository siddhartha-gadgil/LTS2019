#!/bin/bash
set -e
cd Code
# rm *.ibc
for file in *.idr
do
  echo "checking $file"
  idris --check --package contrib "$file"
done
