#!/usr/bin/env python3
# 
# Extract the instructions for a given task from conversion_tasks.md, or list all tasks.
# Usage: python ./get_task.py '<task-title>'   # Output instructions for task.
#        python ./get_task.py next             # Output instructions for the next task following that in status.json, and update status.json.
#        python ./get_task.py list             # List all task titles.
#        python ./get_task.py summary          # Output title and summary for all tasks.
# where <task-title> is the title of the task as it appears in conversion_tasks.md as `## Task: <task-title>`.

# Extract text from `## Task: <task-title>` to the next `## Task:` or end of file.

import sys
import os
import json

script_dir = __file__.rsplit("/", 1)[0]

if len(sys.argv) != 2:
    print("Usage: python ./get_task.py '<task-name>'")
    sys.exit(1)

task_title = sys.argv[1]

next = task_title == "next"
list = task_title == "list"
summary = task_title == "summary"


current_task = None
in_current_task = False

if next:
    # The current directory must contain status.json.
    if not os.path.isfile(f"status.json"):
        print("ERROR: status.json not found.")
        sys.exit(1)

    # Read status.json to get the current task.
    try:
        with open(f"status.json", "r") as f:
            status = json.load(f)
    except Exception as e:
        print(f"ERROR: Must be run from a conversion working directory containing status.json.")
        sys.exit(1)
    current_task = status.get("task", None)
    if not current_task:
        print("ERROR: status.json does not contain 'task'.")
        sys.exit(1)

# Find conversion_tasks.md in the directory of this script.
with open(f"{script_dir}/conversion_tasks.md", "r") as f:
    # Read line-by-line, matching `## Task: `
    in_task = False
    while (line := f.readline()) and not line.startswith("# EOF"):
        line = line.strip()
        if line.startswith("## Task: "):
            title = line[len("## Task: "):]
            if list or summary:
                if summary:
                    # Print the next non-blank line.
                    while not (line := f.readline().strip()):
                        pass
                    if not line.startswith("Summary: "):
                        print(title + ": " + "No summary provided.")
                    if line.strip():
                        print(title + ": " + line[len("Summary: "):].strip())
                else:
                    print(title)
            else:
                if next:
                    if current_task == title:
                        in_current_task = True
                    else:
                        if in_current_task:
                            # We were in the current task, and now we are at the next task,
                            # which is the one we're looking for.
                            in_current_task = False
                            task_title = title
                            # Reset status.json to reflect the new next task.
                            new_status = {}
                            new_status["task"] = task_title
                            new_status["fev.sh"] = "none"
                            new_status["llm"] = ""
                            with open(f"status.json", "w") as f_status:
                                json.dump(new_status, f_status, indent=4)
                in_task = title == task_title
        if in_task:
            print(line)

if next and in_current_task:
    print("Congratulations! You have completed the final task!")
    sys.exit(0)
