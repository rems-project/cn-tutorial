#!/usr/bin/env bash 

BRANCH="main"
INTERVAL="1.month"

# Allow the CI process to pass a location for CN 
if [ -n "$1" ]
then
    echo "using CN=$1 in $PWD"
    CN="$1"
else
    CN="cn verify"
fi

# Generate a list of recently-changed files 
FILES=$(git log --since="$INTERVAL" --name-only --pretty=format: "$BRANCH" | sort | uniq)

# Regexp selecting files in the correct location 
EXAMPLE_RXP="^src/(examples/[^/]+\.c|example-archive/[^/]+/working/[^/]+\.c)$"
# Regexp filtering out files marked 'broken' 
FILTER_RXP="broken\.c$"
# Filter the list for files of interest 
FILTERED_FILES=$(echo "$FILES" | grep -E "$EXAMPLE_RXP" | grep -Ev "$FILTER_RXP")

# Create a temporary directory 
TEMP_DIR=$(realpath "$(mktemp -d ./tmp.XXXXXX)")

# Create a log file listing the locations of SMT logs 
DATE_STRING=$(date +"%Y-%m-%d_%H-%M-%S")
DATE_STRING_SHORT=$(date +"%Y-%m-%d")
echo "# Log date: $DATE_STRING" >> "$TEMP_DIR/manifest.md"
echo "# $(cn --version)" >> "$TEMP_DIR/manifest.md"
echo "" >> "$TEMP_DIR/manifest.md"

ROOT_DIR=$(pwd)
for FILEPATH in $FILTERED_FILES; do 
  if [ -f "$FILEPATH" ]; then
    DIR=$(dirname "$FILEPATH")
    FILE=$(basename "$FILEPATH")

    # Create the log directory for each file 
    LOG_DIR="$TEMP_DIR/$FILEPATH-log"
    mkdir -p "$LOG_DIR"

    cd $DIR 
    # Run CN on the target file 
    $CN "$FILE" --solver-type=cvc5 --solver-logging="$LOG_DIR" --quiet 
    cp "$FILE" "$LOG_DIR"
    cd "$ROOT_DIR"

    # Remove model files - should probably not emit these 
    rm "$LOG_DIR"/model_send*.smt

    # Record the file in the manifest 
    echo "$FILEPATH-log/" >> "$TEMP_DIR/manifest.md" 
  fi 
done 

# Create a zip file and tar.gz file of the SMT logs 
cd "$TEMP_DIR"
zip -r "$ROOT_DIR/${DATE_STRING_SHORT}_CN-SMT-log.zip" *  1>&2 
tar -czvf "$ROOT_DIR/${DATE_STRING_SHORT}_CN-SMT-log.tar.gz" * 1>&2

rm -r "$TEMP_DIR"

echo "$ROOT_DIR/SMT-log-$DATE_STRING.zip"