# author: z5253065 Liqi Jiang
# Sun 28/06/2020

import sys
import re
from collections import defaultdict
from cspProblem import CSP, Constraint
from cspConsistency import Search_with_AC_from_CSP
from searchGeneric import AStarSearcher


class extend_CSP(CSP):
    def __init__(self, domain, constraints, soft_constraint, cost):
        super().__init__(domain, constraints)
        self.soft_constraint = soft_constraint
        self.cost = cost


class Search_with_AC_from_Cost_CSP(Search_with_AC_from_CSP):
    def __init__(self, csp):
        super().__init__(csp)
        self.soft_constraint = soft
        self.task_cost = task_cost

    def heuristic(self, n):
        cost_number = 0
        cost_task_min = {}
        # print("node", n)
        for task_name in n:
            if n[task_name] == set():
                return 0
            if task_name in self.soft_constraint.keys():  # check if the task has soft constraint
                expected_time = self.soft_constraint[task_name]
                cost = []
                for daytime in n[task_name]:
                    exceed_time = daytime[1] - expected_time
                    if exceed_time <= 0:
                        exceed_cost = 0
                    else:
                        if daytime[1]//10 == expected_time // 10:  # at the same day
                            exceed_cost = exceed_time * int(self.task_cost[task_name])
                        else:
                            assist_time = 10*(daytime[1]//10)+ expected_time % 10
                            exceed_time = 24*(daytime[1]//10-expected_time//10)-(assist_time - daytime[1])
                            exceed_cost = exceed_time * int(self.task_cost[task_name])
                    cost.append(exceed_cost)
                cost_task_min.update({task_name: int(min(cost))})
        for key in cost_task_min.keys():
            cost_number += cost_task_min[key]
        return cost_number


# binary constraints
def before(t1, t2):  # t1 ends when or before t2 starts
    return t1[1] <= t2[0]


def after(t1, t2):  # t1 starts after or when t2 ends
    return t1[0] >= t2[1]


def same_day(t1, t2):  # t1 and t2 are scheduled on the same day
    return t1[0]//10 == t2[0]//10


def starts_at(t1, t2):  # t1 starts exactly when t2 ends
    return t1[0] == t2[1]


# hard domain constraints
def day_(day):  # t starts on given day at any time
    def dayt(t):
        return t[0]//10 == day
    return dayt


def time_(time):  # t starts at given time on any day
    def timet(t):
        return t[0] % 10 == time
    return timet


def start_before_range(day, time):
    def startbeforerange(t):
        return t[0] <= 10*day + time
    return startbeforerange


def start_after_range(day, time):
    def startafterrange(t):
        return t[0] >= 10*day + time
    return startafterrange


def end_before_range(day, time):
    def endbeforerange(t):
        return t[1] <= 10 * day + time
    return endbeforerange


def end_after_range(day, time):
    def endafterrange(t):
        return t[1] >= 10 * day + time
    return endafterrange


def start_in(daytime1, daytime2):
    def startin(t):
        return daytime1 <= t[0] <= daytime2
    return startin


def end_in(daytime1, daytime2):
    def endin(t):
        return daytime1 <= t[1] <= daytime2
    return endin


def start_before(time):
    def startbefore(t):
        return t[0] % 10 <= time
    return startbefore


def end_before(time):
    def endbefore(t):
        return t[1] % 10 <= time
    return endbefore


def start_after(time):
    def startafter(t):
        return t[0] % 10 >= time
    return startafter


def end_after(time):
    def endafter(t):
        return t[1] % 10 >= time
    return endafter


# find the key according the value
def find_key(dict, value):
    for k, v in dict.items():
        if v == value:
            return k


# process the input file
days = {"mon": 1, "tue": 2, "wed": 3, "thu": 4, "fri": 5}
times = {"9am": 1, "10am": 2, "11am": 3, "12pm": 4, "1pm": 5, "2pm": 6, "3pm": 7, "4pm": 8, "5pm": 9}
filename = sys.argv[1]
# filename = "test4.txt"
file = open(filename, 'r')
task_duration = {}
task_domain = {}  # save domain of csp
hard = []  # save binary constraints and hard domain constraints
soft = {}
task_cost = {}
# delete start #
pattern0 = re.compile(r'^[\s]*#')
# task pattern
pattern1 = re.compile(r'^[\s]*task,[\s]+([\S]+)[\s]+([\S]+)[\s]*$')
# binary constraints pattern
pattern2 = re.compile(r'^[\s]*constraint,[\s]+([\S]+)[\s]+([\S]+)[\s]+([\S]+)[\s]*$')
# hard domain constraints
pattern3 = re.compile(r'^[\s]*domain,[\s]+([\S]+)[\s]+(.*)[\s]*$')
# soft constraints pattern
pattern4 = re.compile(r'^[\s]*domain,[\s]+([\S]+)[\s]+ends-by[\s]+(.*)[\s]*$')
for line in file:
    if pattern0.match(line):
        continue
    if pattern1.match(line):
        task_name = pattern1.match(line).group(1)
        duration = int(pattern1.match(line).group(2))
        task_duration.update({task_name: duration})
        task_domain[task_name] = set()
        for i in days.values():
            for j in times.values():
                if j + duration > 9:
                    break
                else:
                    task_domain[task_name].add((i * 10 + j, i * 10 + j + duration))
        continue
    if pattern2.match(line):
        task1 = pattern2.match(line).group(1)
        task2 = pattern2.match(line).group(3)
        relation = pattern2.match(line).group(2)
        # C0 = Constraint(('A','B'),lt)
        if relation == "before":
            hard.append(Constraint((task1, task2), before))
            continue
        if relation == "after":
            hard.append(Constraint((task1, task2), after))
            continue
        if relation == "same-day":
            hard.append(Constraint((task1, task2), same_day))
            continue
        if relation == "starts-at":
            hard.append(Constraint((task1, task2), starts_at))
            continue
    if pattern4.match(line):
        task_name = pattern4.match(line).group(1)
        day = pattern4.match(line).group(2).strip().split()[0]
        time = pattern4.match(line).group(2).strip().split()[1]
        cost = pattern4.match(line).group(2).strip().split()[2]
        soft[task_name] = days[day]*10 + times[time]
        task_cost[task_name] = cost
        continue
    if pattern3.match(line):
        task_name = pattern3.match(line).group(1)
        if pattern3.match(line).group(2).strip() in days.keys():
            # C1 = Constraint(('B',), ne_(2))
            day = days[pattern3.match(line).group(2).strip()]
            hard.append(Constraint((task_name,), day_(day)))
            continue
        if pattern3.match(line).group(2).strip() in times.keys():
            time = times[pattern3.match(line).group(2).strip()]
            hard.append(Constraint((task_name,), time_(time)))
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "starts-before" and pattern3.match(line).group(2).strip().split()[1] in days.keys():
            day = days[pattern3.match(line).group(2).strip().split()[1]]
            time = times[pattern3.match(line).group(2).strip().split()[2]]
            hard.append(Constraint((task_name,), start_before_range(day, time)))  # at or before given time
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "starts-after" and pattern3.match(line).group(2).strip().split()[1] in days.keys():
            day = days[pattern3.match(line).group(2).strip().split()[1]]
            time = times[pattern3.match(line).group(2).strip().split()[2]]
            hard.append(Constraint((task_name,), start_after_range(day, time)))  # at or after given time
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "ends-before" and pattern3.match(line).group(2).strip().split()[1] in days.keys():
            day = days[pattern3.match(line).group(2).strip().split()[1]]
            time = times[pattern3.match(line).group(2).strip().split()[2]]
            hard.append(Constraint((task_name,), end_before_range(day, time)))  # at or before given time
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "ends-after" and pattern3.match(line).group(2).strip().split()[1] in days.keys():
            day = days[pattern3.match(line).group(2).strip().split()[1]]
            time = times[pattern3.match(line).group(2).strip().split()[2]]
            hard.append(Constraint((task_name,), end_after_range(day, time)))  # at or after given time
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "starts-in":
            daytime1 = 10*days[pattern3.match(line).group(2).strip().split()[1]]+times[pattern3.match(line).group(2).strip().split()[2].split('-')[0]]
            daytime2 = 10*days[pattern3.match(line).group(2).strip().split()[2].split('-')[1]]+times[pattern3.match(line).group(2).strip().split()[3]]
            hard.append(Constraint((task_name,), start_in(daytime1, daytime2)))  # day-time range
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "ends-in":
            daytime1 = 10*days[pattern3.match(line).group(2).strip().split()[1]]+times[pattern3.match(line).group(2).strip().split()[2].split('-')[0]]
            daytime2 = 10*days[pattern3.match(line).group(2).strip().split()[2].split('-')[1]]+times[pattern3.match(line).group(2).strip().split()[3]]
            hard.append(Constraint((task_name,), end_in(daytime1, daytime2)))  # day-time range
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "starts-before":
            time = times[pattern3.match(line).group(2).strip().split()[1]]
            hard.append(Constraint((task_name,), start_before(time)))  # at or before time on any day
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "ends-before":
            time = times[pattern3.match(line).group(2).strip().split()[1]]
            hard.append(Constraint((task_name,), end_before(time)))  # at or before time on any day
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "starts-after":
            time = times[pattern3.match(line).group(2).strip().split()[1]]
            hard.append(Constraint((task_name,), start_after(time)))  # at or after time on any day
            continue
        if pattern3.match(line).group(2).strip().split()[0] == "ends-after":
            time = times[pattern3.match(line).group(2).strip().split()[1]]
            hard.append(Constraint((task_name,), end_after(time)))  # at or after time on any day
            continue
# print(task_duration)
# print(task_domain)
# print(hard)
# print(soft)
# print(task_cost)
csp = extend_CSP(task_domain, hard, soft, task_cost)
problem = Search_with_AC_from_Cost_CSP(csp)
schr1 = AStarSearcher(problem)
solution = schr1.search()
if solution:
    # print(solution)
    for task_name in task_duration.keys():
        for daytime in solution.end()[task_name]:
            # print(daytime)
            print(task_name, ":", find_key(days, daytime[0] // 10), " ", find_key(times, daytime[0] % 10), sep="")
    print("cost:", problem.heuristic(solution.end()), sep="")
else:
    print("No solution")





