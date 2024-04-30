process_files() {
  local dir=$1
  local pattern=$2
  local action=$3
  local expected_exit_code=$4 

  if [ -d "$dir" ]; then 
    # Array to hold files matching the pattern
    local files=($(find "$dir" -maxdepth 1 -type f -name "$pattern" | sort))
    
    # Check if the array is not empty
    if [ "${#files[@]}" -gt 0 ]; then
      for file in "${files[@]}"; do
        # Ensure the file variable is not empty
        if [[ -n "$file" ]]; then
          "$action" "$file" "$expected_exit_code"
        fi
      done
    else
      echo "No files matching '$pattern' found in $dir"
    fi
  else 
    echo "Directory $dir does not exist" 
  fi 
}

failures=0

check_file() {
  local file=$1
  local expected_exit_code=$2

  printf "[$file]... "
  timeout 10 cn "$file" > /dev/null 2>&1
  local result=$?

  if [ $result -eq $expected_exit_code ]; then
    printf "\033[32mPASS\033[0m\n"
  else
    printf "\033[31mFAIL\033[0m (Unexpected return code: $result)\n"
    failures=$(( $failures + 1 ))
  fi
}

process_files "working" "*.c" check_file 0
process_files "broken/error-cerberus" "*.c" check_file 2 
process_files "broken/error-crash" "*.c" check_file 125
process_files "broken/error-proof" "*.c" check_file 1
process_files "broken/error-timeout" "*.c" check_file 124

if [[ "$failures" = 0 ]]
then
  exit 0
else
  exit 1
fi
