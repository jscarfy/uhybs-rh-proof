import math
import matplotlib.pyplot as plt
import numpy as np

def zeta_weight(t):
    return 1 / (1 + t**2)

def simulate_sigma_UHYBS(n, t, methods, ts):
    weights = [zeta_weight(tj) for tj in ts]
    total_weight = sum(weights)
    if total_weight == 0:
        return sum(m(n) for m in methods) / len(methods)
    weights = [w / total_weight for w in weights]
    return sum(w * m(n) for w, m in zip(weights, methods))

def alt_seq_mean(n):
    return sum([(-1)**k for k in range(n)]) / n if n > 0 else 0

def sin2n_seq_mean(n):
    return sum([math.sin(2**k) for k in range(n)]) / n if n > 0 else 0

methods = [alt_seq_mean, sin2n_seq_mean]
ts = [1.0, 3.0]
t_vals = np.linspace(0.1, 10, 200)
n_values = [50, 100, 200]

plt.figure(figsize=(12, 6))
for n in n_values:
    sigma_vals = [simulate_sigma_UHYBS(n, t, methods, ts) for t in t_vals]
    plt.plot(t_vals, sigma_vals, label=f"n = {n}")
plt.axhline(0.5, color='red', linestyle='--', label='Target Mean (0.5)')
plt.xlabel("t")
plt.ylabel(r"$\sigma_n^{\mathrm{UHYBS}}(t)$")
plt.title("Behavior of $\sigma_n^{\mathrm{UHYBS}}(t)$ for Multiple n Values")
plt.legend()
plt.grid(True)
plt.tight_layout()
plt.savefig("uhybs_rh_plot.png")
plt.show()