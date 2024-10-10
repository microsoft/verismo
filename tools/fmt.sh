# Determine the directory that this script is in
if [ "$BASH_VERSION" ]; then
  SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
elif [ "$ZSH_VERSION" ]; then
  SCRIPT_DIR="$( cd "$( dirname "${(%):-%N}" )" >/dev/null 2>&1 && pwd )"
else
  echo "Unknown shell; exiting."
  return 1
fi

TOOLS_DIR=$SCRIPT_DIR

SOURCE_DIR=$TOOLS_DIR/../source/verismo
for f in `find $SOURCE_DIR -type f -name "*.rs"`
do
output=$(verusfmt $f $1 2>&1)
if [ $? -ne 0 ]; then
    # Check if the output contains "Failed to parse"
    if echo "$output" | grep -q "Failed to parse"; then
      echo "Continuing despite parse failure: $output"
    else
      echo "Error occurred: $output"
      exit 1
    fi
fi
done