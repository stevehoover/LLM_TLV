#!/usr/bin/env python3

import sys
import os
import json
import subprocess

script_dir = __file__.rsplit("/", 1)[0]

if len(sys.argv) != 2:
    print("get_task.py Help")
    print("----------------")
    print("Extract the instructions for a given task from conversion_tasks.md, or list all tasks.")
    print("Run from a module conversion directory. The current task is defined in ./status.json.")
    print("")
    print("Usage: ./scripts/get_task.py <task/command>")
    print("")
    print("Formats:")
    print("    ./scripts/get_task.py list           # List all task names (from `conversion_tasks.md`).")
    print("    ./scripts/get_task.py summary        # Output name and summary for all tasks.")
    print("    ./scripts/get_task.py '<task-name>'  # Get instructions for the given task name, given as it appears in")
    print("                                         # conversion_tasks.md as `## Task: <task-name>`.")
    print("    ./scripts/get_task.py current        # Get instructions for the current task (defined in `status.json`).")
    print("    ./scripts/get_task.py next           # Move on to and output the next task, updating `status.json`.")
    sys.exit(1)

task_title = sys.argv[1]

current = task_title == "current"
next = task_title.startswith("next")
force_next = task_title == "next!"
list = task_title == "list"
summary = task_title == "summary"

task_printed = False


current_task = None
in_current_task = False

if next or current:
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
    # Translate "current" to the actual current task title (then, its no longer a special case).
    if task_title == "current":
        task_title = current_task

# Find conversion_tasks.md in the instructions directory.
with open(f"{script_dir}/../instructions/conversion_tasks.md", "r") as f:
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
                            # Move on to and report the next task, but only if `wip.tlv` matches `feved.tlv` and
                            # the last task was completed successfully or it was not run for this task (nothing to be done).
                            # When the agent tries to move on too early, this is a good indication that it has
                            # forgotten its mission in life, so this is a good time to remind it.
                            # Run diff to check if wip.tlv matches feved.tlv.
                            fev_status = status.get("fev.sh", "")
                            diff_status = os.system("diff -q wip.tlv feved.tlv > /dev/null 2>&1")
                            if force_next or ((diff_status == 0) and (fev_status == "none" or fev_status.startswith("0:"))):
                                # OK to move on to the next task.
                                # Record a history snapshot for the task we are completing if the
                                # flow did not already record one for it (a no-op task that ran no
                                # FEV). This keeps the console's task flow complete; record_history.sh
                                # selects the next history directory.
                                latest_recorded = None
                                if os.path.isdir("history"):
                                    nums = sorted(d for d in os.listdir("history") if d.isdigit())
                                    if nums:
                                        try:
                                            with open(os.path.join("history", nums[-1], "status.json")) as f_hist:
                                                latest_recorded = json.load(f_hist).get("task")
                                        except (OSError, ValueError):
                                            latest_recorded = None
                                if current_task and latest_recorded != current_task:
                                    subprocess.run([os.path.join(script_dir, "record_history.sh")], check=False)
                                task_title = title
                                # Reset status.json to reflect the new next task.
                                new_status = {}
                                new_status["task"] = task_title
                                new_status["fev.sh"] = "none"
                                new_status["fev_cnt"] = 0
                                new_status["llm"] = ""
                                with open(f"status.json", "w") as f_status:
                                    json.dump(new_status, f_status, indent=4)
                            else:
                                print("")
                                print("Whoa! Hold up! FEV was not run successfully.")
                                print("Refusing to proceed to the next task.")
                                print("")
                                print("IMPORTANT:")
                                print("You MUST reread 'instructions/desktop_agent_instructions.md', then review the current task by")
                                print("running './scripts/get_task.py current' before continuing!!! You may, in the meantime,")
                                print("update 'tracker.md' and 'status.json' and stop working to await guidance.")
                                sys.exit(1)
                in_task = title == task_title
        if in_task:
            print(line)
            task_printed = True

# Print project-specific instructions for this task, if they exist.
if task_printed:
    instructions_file = f"../project_instructions/project_specific_instructions.md"
    if os.path.isfile(instructions_file):
        # Extract instructions from `## Task: <task-name>` until next `## `.
        with open(instructions_file, "r") as f:
            in_task = False
            while (line := f.readline()):
                line = line.rstrip()
                if line.startswith("## "):
                    if line.startswith("## Task: "):
                        title = line[len("## Task: "):]
                        in_task = title == task_title
                        print("")
                        print(f"There are some project-specific instructions for this task:")
                    if in_task:
                        print(line)
                elif in_task:
                    print(line)

if next and in_current_task:
    print("")
    print("Congratulations! You have completed the final task!")
    sys.exit(0)
