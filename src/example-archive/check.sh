check_file() {
  local file=$1
  local expected_exit_code=$2

  printf "[$file]... "
  timeout 60 cn "$file" > /dev/null 2>&1
  result=$?
  if [ $result -eq $expected_exit_code ]; then
    echo "\033[32mPASS\033[0m"
  else
    echo "\033[31mFAIL\033[0m (Unexpected error: $result)"
  fi
}

for file in working/*.c; do
  check_file "$file" 0 
done

for file in broken/error-cerberus/*.c; do
  check_file "$file" 2 
done

for file in broken/error-crash/*.c; do
  check_file "$file" 125 
done

for file in broken/error-proof/*.c; do
  check_file "$file" 1 
done

for file in broken/error-timeout/*.c; do
  check_file "$file" 124
done

