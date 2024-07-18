#!/usr/bin/env bash 

BRANCH="main"
INTERVAL="1.month"

if [ -n "$1" ]
then
    echo "using CN=$1 in $PWD"
    CN="$1"
else
    CN="cn"
fi

EXAMPLE_RXP="^src/(examples/[^/]+\.c|example-archive/[^/]+/working/[^/]+\.c)$"
FILTER_RXP="broken\.c$"

FILES=$(git log --since="$INTERVAL" --name-only --pretty=format: "$BRANCH" | sort | uniq)
FILTERED_FILES=$(echo "$FILES" | grep -E "$EXAMPLE_RXP" | grep -Ev "$FILTER_RXP")

TEMP_DIR=$(realpath "$(mktemp -d ./tmp.XXXXXX)")
ROOT_DIR=$(pwd)

LOGGED_FILES=""

for FILEPATH in $FILTERED_FILES; do 
  if [ -f "$FILEPATH" ]; then
    DIR=$(dirname "$FILEPATH")
    FILE=$(basename "$FILEPATH")

    LOG_DIR="$TEMP_DIR/$FILEPATH-log"
    mkdir -p "$LOG_DIR"

    cd $DIR 
    $CN "$FILE" --solver-type=cvc5 --solver-logging="$LOG_DIR"
    cp "$FILE" "$LOG_DIR"
    cd "$ROOT_DIR"

    LOGGED_FILES="$LOGGED_FILES $FILEPATH-log/" 
  fi 
done 

DATE_STRING=$(date +"%Y-%m-%d_%H-%M-%S")
echo "Log date: $DATE_STRING" >> "$TEMP_DIR/manifest.txt"
echo "" >> "$TEMP_DIR/manifest.txt"

for FILE in $LOGGED_FILES; do 
  echo "$FILE" >> "$TEMP_DIR/manifest.txt"
done 

cd "$TEMP_DIR"
zip -r "$ROOT_DIR/SMT-log-$DATE_STRING.zip" ./* 

rm -r "$TEMP_DIR"