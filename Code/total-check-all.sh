for file in *.idr
do
  echo "checking $file"
  idris --check --total --package contrib "$file"
done
