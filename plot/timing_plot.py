from typing import Sequence
import dataclasses
import numpy as np
import matplotlib.pyplot as plt
import matplotlib
from collections import Counter
matplotlib.rcParams['pdf.fonttype'] = 42
matplotlib.rcParams['ps.fonttype'] = 42

@dataclasses.dataclass
class Result:
    theory: str
    num_of_tasks: int
    has_warning: bool
    time: float
    succeeded: bool


@dataclasses.dataclass
class Rule:
    name: str
    results: list[Result]
    succeeeded: bool
    def all_same_num_of_tasks(self) -> bool:
        return all(x.num_of_tasks == self.results[0].num_of_tasks for x in self.results)
    def first_num_of_tasks(self) -> int:
        return self.results[0].num_of_tasks
    def overall_time(self) -> float:
        return sum(x.time for x in self.results)

# TODO: Handle ANSI color escape codes
def parse_file(lines: Sequence[str]) -> list[Rule]:
    """
    The file looks like this:
    ====> Slice(Concat(A,B), A.size, A.size+B.size) ⇒ B
    >>> Bool
    [INFO-Bool]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
    [INFO-Bool]: Number of bounded verification tasks: 1
    [SUCCESS-Bool]: [0.12387501999910455s] Verification succeeded.
    >>> Int
    [INFO-Int]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
    [INFO-Int]: Number of bounded verification tasks: 1
    [SUCCESS-Int]: [0.11165066000830848s] Verification succeeded.
    >>> Real
    [INFO-Real]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
    [INFO-Real]: Number of bounded verification tasks: 1
    [SUCCESS-Real]: [0.106301934007206s] Verification succeeded.
    >>> Overall
    [SUCCESS-Overall]: [0.34182761401461903s] Verification succeeded.
    ====> Slice(Broadcast(A)) ⇒ Broadcast(A)
    >>> Bool
    [INFO-Bool]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
    [INFO-Bool]: Number of bounded verification tasks: 1
    [SUCCESS-Bool]: [0.34009405800316017s] Verification succeeded.
    >>> Int
    [INFO-Int]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
    [INFO-Int]: Number of bounded verification tasks: 1
    [SUCCESS-Int]: [0.23800732199742924s] Verification succeeded.
    >>> Real
    [INFO-Real]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
    [INFO-Real]: Number of bounded verification tasks: 1
    [SUCCESS-Real]: [0.26108629700320307s] Verification succeeded.
    >>> Overall
    [SUCCESS-Overall]: [0.8391876770037925s] Verification succeeded.
    """

    rules: list[Rule] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("====>"):
            name = " ".join(line.split(" ")[1:])
            results: list[Result] = []
            has_warning = False
            i += 1
            while i < len(lines) and not lines[i].startswith("====>"):
                if lines[i].startswith(">>>"):
                    theory = lines[i].split(" ")[1].strip()
                    if theory != "Overall":
                        i += 1
                        if lines[i].startswith("[FAIL"):
                            time = float(lines[i].split(" ")[1][1:-2])
                            results.append(Result(theory, -1, False, time, False))
                            i += 1
                            continue
                        i += 1
                        num_of_tasks = int(lines[i].split(" ")[-1])
                        i += 1
                        while lines[i].startswith("[WARNING"):
                            has_warning = True
                            i += 1
                        time = float(lines[i].split(" ")[1][1:-2])
                        succeeded = lines[i].startswith("[SUCCESS")
                        results.append(
                            Result(theory, num_of_tasks, has_warning, time, succeeded))
                    else:
                        i += 1
                        time = float(lines[i].split(" ")[1][1:-2])
                        succeeded = lines[i].startswith("[SUCCESS")
                        rules.append(Rule(name, results, succeeded))
                        i += 1
                        break
                else:
                    # No theory is given
                    i += 1
                    num_of_tasks = int(lines[i].split(" ")[-1])
                    i += 1
                    while lines[i].startswith("[WARNING"):
                        has_warning = True
                        i += 1
                    time = float(lines[i].split(" ")[1][1:-2])
                    succeeded = lines[i].startswith("[SUCCESS")
                    results.append(Result("", num_of_tasks, has_warning, time, succeeded))
                    rules.append(Rule(name, results, succeeded))
                    i += 1
                    break
                i += 1
        else:
            i += 1
    return rules


sample = """====> Slice(Concat(A,B), A.size, A.size+B.size) ⇒ B
>>> Bool
[INFO-Bool]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
[INFO-Bool]: Number of bounded verification tasks: 1
[SUCCESS-Bool]: [0.12387501999910455s] Verification succeeded.
>>> Int
[INFO-Int]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
[INFO-Int]: Number of bounded verification tasks: 1
[SUCCESS-Int]: [0.11165066000830848s] Verification succeeded.
>>> Real
[INFO-Real]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
[INFO-Real]: Number of bounded verification tasks: 1
[SUCCESS-Real]: [0.106301934007206s] Verification succeeded.
>>> Overall
[SUCCESS-Overall]: [0.34182761401461903s] Verification succeeded.
====> Slice(Broadcast(A)) ⇒ Broadcast(A)
>>> Bool
[INFO-Bool]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
[INFO-Bool]: Number of bounded verification tasks: 1
[SUCCESS-Bool]: [0.34009405800316017s] Verification succeeded.
>>> Int
[INFO-Int]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
[INFO-Int]: Number of bounded verification tasks: 1
[SUCCESS-Int]: [0.23800732199742924s] Verification succeeded.
>>> Real
[INFO-Real]: Inferred bounds: fromList [(rclass1,1),(rclass0,1)]
[INFO-Real]: Number of bounded verification tasks: 1
[SUCCESS-Real]: [0.26108629700320307s] Verification succeeded.
>>> Overall
[SUCCESS-Overall]: [0.8391876770037925s] Verification succeeded.
""".splitlines()
# print(parse_file(sample))
with open("result.txt", "r") as f:
    res = parse_file(list(map(lambda x: x.strip(), f.readlines())))

number_of_failed_inference = len(list(filter(lambda x: x < 0, map(lambda x: x.first_num_of_tasks(), res))))
number_of_tasks = list(filter(lambda x: x >= 0, map(lambda x: x.first_num_of_tasks(), res)))
success = list(filter(lambda x: x.succeeeded, res))

times = list(map(lambda x: x.overall_time(), success))

def print_stats(success):
    times = list(map(lambda x: x.overall_time(), success))
    print(f'Number of verified rules: {len(times)}')
    print(f'Max time: {max(times)}')
    print(f'Min time: {min(times)}')
    print(f'Average time: {sum(times) / len(times)}')
    print(f'Geometric mean: {np.exp(np.mean(np.log(times)))}')
    print(f'Number of rules verified under 1s: {len(list(filter(lambda x: x < 1, times)))}')
    print(f'Number of rules verified under 5s: {len(list(filter(lambda x: x < 5, times)))}')

    assert(all(list(map(lambda x: x.all_same_num_of_tasks(), success))))
    num_tasks_freq = Counter(list(map(lambda x: x.first_num_of_tasks(), success)))
    for key, value in num_tasks_freq.items():
        print(f'Number of rules with {key} tasks: {value}')

    tasks = sorted(num_tasks_freq.keys())
    values = [num_tasks_freq[t] for t in tasks]
    tasks = [str(t) for t in tasks]
    plt.figure(figsize=(3,2))
    plt.bar(tasks, values, label="AQP", color='C0')
    plt.xticks(tasks)
    plt.ylim(0, max(values) * 1.2)

    for t in tasks:
        plt.text(t, num_tasks_freq[int(t)] + 0.5, str(num_tasks_freq[int(t)]), ha='center', va='bottom')

    plt.ylabel('Number of Rules')
    plt.xlabel('Number of Tasks')
    plt.savefig('num_tasks.pdf', bbox_inches='tight', dpi=600, pad_inches=0)
    plt.clf()

def plot_hist(times):
    bins = np.logspace(np.log10(0.001),np.log10(max(t for t in times)), 5)

    plt.hist(times, bins=20, edgecolor='black')

    plt.title('Total Time taken for Unbounded Verification')
    plt.xlabel('Time (seconds)')
    plt.ylabel('Number of Rules')

    plt.savefig('timing_plot.pdf', format="pdf", bbox_inches="tight", dpi=600)
    plt.clf()

def plot_cdf(times):
    times = sorted(times)
    yvals = np.arange(len(times))/float(len(times))
    plt.figure(figsize=(3,2))
    plt.grid()
    plt.xscale("log")
    plt.yticks([0.2 * i for i in range(6)])
    plt.ylim(0,1)
    plt.xlabel(" Total Verification Time (s)")
    plt.ylabel("CDF")
    plt.xticks([0.1, 1, 10], ['0.1', '1', '10'])
    plt.plot(times, yvals, color='C0')
    plt.savefig("timing_plot.pdf", format="pdf", bbox_inches='tight', dpi=600, pad_inches=0)
    plt.clf()

print_stats(success)
plot_cdf(times)
