for i in $( find src -name "*.agda" | sed 's/src\/\(.*\)\.agda/\1/' | sed 's/\//\./g' | sort ); do
  echo "import $i" >> index.agda;
done
