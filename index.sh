for i in $( find src -name "*.agda" | grep -v "index.agda" | sed 's/src\/\(.*\)\.agda/\1/' | sed 's/\//\./g' | sort ); do
  echo "import $i" >> src/index.agda;
done
