"""
alpha_pipeline: Pipeline evolutivo híbrido para diseño de microservicios.
"""

__version__ = "0.1.0"

from .metrics import lcom, sgm, noo, coupling_out, sgm_sd
from .runner import main
