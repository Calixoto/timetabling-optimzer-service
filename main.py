import re
import subprocess
from collections import defaultdict
from fastapi import FastAPI
import uuid

app = FastAPI()

def read_data(file_path):
    with open(file_path, 'r') as file:
        data = file.read()

    class_schedules = re.findall(
        r'<(\d+) (\d+) "(.*?)" (\d+) "(.*?)" "(.*?)" (\d+)>', data)

    schedule_table = defaultdict(lambda: defaultdict(list))

    for semester, class_id, class_name, day, shift, room, room_space in class_schedules:
        schedule_table[int(semester)][(int(day), shift)].append(
            (class_id, class_name, room, int(room_space)))

    return schedule_table

def create_objects_array(schedule_table):
    objects_array = []

    for semester, days in schedule_table.items():
        for (day, shift), classes in days.items():
            for class_id, class_name, room, room_space in classes:
                class_obj = {
                    "semester": semester,
                    "day": day,
                    "shift": shift,
                    "class_id": class_id,
                    "class_name": class_name,
                    "room": room,
                    "room_space": room_space
                }
                objects_array.append(class_obj)

    return objects_array

def create_filtered_objects_array(schedule_table):
    days_of_week = {1: "SEG", 2: "TER", 3: "QUA", 4: "QUI", 5: "SEX", 6: "SAB"}
    possible_shifts = ["M12", "M34", "M56", "T12", "T34", "T56", "N12", "N34"]

    filtered_objects_array = []

    for day in range(1, 7):
        for shift in possible_shifts:
            objects_array = []

            for semester, days in schedule_table.items():
                for (current_day, current_shift), classes in days.items():
                    if current_day == day and current_shift == shift:
                        for class_id, class_name, room, room_space in classes:
                            class_obj = {
                                "semester": semester,
                                "class_id": str(uuid.uuid4()),
                                "class_name": class_name,
                                "room": room,
                                "schedule": shift,
                                "room_space": room_space
                            }
                            objects_array.append(class_obj)

            obj = {
                "weekday": days_of_week.get(day),
                "schedule": shift,
                "id": str(uuid.uuid4()),
                "courses": objects_array
            }

            filtered_objects_array.append(obj)

    return filtered_objects_array

schedule_order = {
   "M12": 0,
   "M34": 1,
   "M56": 2,
   "T12": 3,
   "T34": 4,
   "T56": 5,
   "N12": 6,
   "N34": 7
}

@app.get("/schedule")
def get_schedule():
    generate_file()
    schedule_table = read_data('model_runner_toy.txt')
    filtered_objects_array = create_filtered_objects_array(schedule_table)
    sorted_data = sorted(filtered_objects_array, key=lambda x: schedule_order[x["schedule"]])
    # data.sort(key=lambda x: schedule_order[x["schedule"]])
    return sorted_data

def generate_file():
    command = ['oplrun', '-D', 'output_fileName="model_runner_toy.txt"', 'TimeTabling.mod', 'TimeTabling_toy.dat']
    subprocess.run(command, check=True)
