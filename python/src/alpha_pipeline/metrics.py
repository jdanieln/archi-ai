from typing import List, Dict
import numpy as np

def lcom(ops: List[Dict]) -> float:
    M = len(ops)
    all_params = [p for op in ops for p in op["params"]]
    F = len(set(all_params))
    MF = sum(len(op["params"]) for op in ops)
    if M == 0 or F == 0:
        return 1.0
    return 1 - (MF) / (M*F)

# SGM y NOO analogamente...
def noo(ops: List[Dict]) -> int:
    return len(ops)


def sgm(ops: List[Dict]) -> float:
    # implementación simplificada: media de (#params)/F + peso CRUD normalizado
    F = len({p for op in ops for p in op["params"]}) or 1
    weights = {"create":4,"update":3,"delete":2,"read":1}
    vals = []
    for op in ops:
        fg = weights.get(op["name"].lower(), 1)
        dg = len(op["params"])/F
        vals.append((fg + dg)/2)
    return float(np.mean(vals)) if vals else 0.0

def normalize(x, xmin, xmax):
    return (x - xmin)/(xmax - xmin) if xmax > xmin else 0.0

# Métrica de acoplamiento (fan-out)
def coupling_out(svc: str, calls: List[Dict]) -> int:
    """
    Número de servicios distintos a los que 'svc' invoca.
    calls = [ {"from": str, "to": str}, ... ]
    """
    return len({ c["to"] for c in calls if c["from"] == svc })

# Desviación estándar de granularidad (SGM-σ)
def sgm_sd(ops: List[Dict]) -> float:
    """
    Desviación estándar de la granularidad funcional (SGM_op) de cada operación
    respecto a la media SGM.
    """
    M = len(ops)
    if M == 0:
        return 0.0
    # recalcular F
    F = len({ p for op in ops for p in op["params"] }) or 1
    # calcular granularidades
    weights = {"create":4,"update":3,"delete":2,"read":1}
    gs = []
    for op in ops:
        fg = weights.get(op["name"].lower(), 1)
        dg = len(op["params"]) / F
        gs.append((fg + dg) / 2)
    mean = float(np.mean(gs))
    var = float(np.mean([(g-mean)**2 for g in gs]))
    return var** 0.5