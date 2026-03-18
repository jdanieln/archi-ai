# ArchiGenMS (Research Project)

**Repository Name**: `archi-ai`

ArchiGenMS is a research project that leverages Artificial Intelligence and Evolutionary Computing to automatically design microservice architectures from user stories. The system uses **Lean 4** for formal validation of the generated architectures, ensuring their correctness and structural quality.

## ✨ Main Features

*   **Automated Architecture Design**: Generates microservice architectures from natural language user stories.
*   **Evolutionary Approach**: Implements a genetic algorithm that explores the solution space to find optimal designs, guided by software quality metrics.
*   **LLM Integration**: Utilizes Large Language Models (such as **Gemini 3.1 Pro Preview** and **GPT-5.1**) to interpret requirements and propose initial candidates and mutations.
*   **Formal Validation**: Integrates the **Lean 4** proof assistant to mathematically validate the structure and calculate precise metrics (LCOM, SGM, Coupling).

## 🛠️ Technologies Used

*   **Main Language**: Python 3.x
*   **Formal Validation**: [Lean 4](https://leanprover.github.io/)
*   **Artificial Intelligence**: 
    *   Google Generative AI (`gemini-3.1-pro-preview`)
    *   OpenAI API / LiteLLM (`gpt-5.1`)
*   **Key Libraries**:
    *   `numpy`, `networkx`, `nltk` (Analysis and Evolution)
    *   `pandas` (Data processing)
    *   `python-dotenv` (Configuration management)
    *   `litellm` (Multi-provider LLM support)

## 📂 Project Structure

```
archi-ai/
├── data/
│   └── user-stories-datasets/  # Datasets with user stories (.txt)
├── python/
│   ├── experiments/            # Results: best architectures (JSON) and metrics (CSV)
│   │   └── exec_20260313_215724/ # Latest consolidated experiment results
│   ├── formal/                 # Lean 4 code for validation and metrics
│   │   ├── src/
│   │   │   ├── ValidateGenotype.lean
│   │   │   └── ServiceMetrics.lean
│   │   └── lakefile.lean       # Lean project configuration
│   ├── src/
│   │   └── alpha_pipeline/     # Evolutionary algorithm logic
│   │       ├── runner.py       # Main delivery script
│   │       └── recovery_runner.py # specialized script for partial/recovery runs
│   ├── .venv_recovery/         # Recommended virtual environment
│   └── requirements.txt        # Python dependencies
├── .env                        # Environment variables (API Keys)
├── README.md                   # This file (English)
└── README_es.md                # Spanish version
```

## 🚀 Getting Started

### Prerequisites

1.  **Python 3.10+**
2.  **Lean 4**: Installed via [elan](https://github.com/leanprover/elan).
3.  **API Keys**: `GEMINI_API_KEY` and/or `OPENAI_API_KEY` are required.

### Installation

1.  **Clone the repository:**

    ```bash
    git clone https://github.com/jdanieln/archi-ai.git
    cd archi-ai
    ```

2.  **Set up the Python environment:**

    ```bash
    cd python
    python3 -m venv .venv_recovery
    source .venv_recovery/bin/activate
    pip install -r requirements.txt
    ```

3.  **Build the Lean project:**
    You must compile the formal validator before running the pipeline.

    ```bash
    cd formal
    lake build
    cd ../..
    ```

4.  **Configure environment variables:**
    Create a `.env` file in the root directory:

    ```bash
    GEMINI_API_KEY='your_api_key_here'
    OPENAI_API_KEY='your_api_key_here'
    ```

## 🏃‍♂️ Usage

To run the evolutionary pipeline and generate an architecture for all datasets:

```bash
cd python
source .venv_recovery/bin/activate
python src/alpha_pipeline/runner.py
```

### Recovery Actions
If an experiment fails mid-run (e.g., due to API quotas), you can use the specialized recovery script to resume from a specific story without losing previous data:

```bash
python src/alpha_pipeline/recovery_runner.py
```
*Note: This script is currently configured to target specific failed stories like `g28-zooniverse`.*

### Results
Results are stored in `python/experiments/exec_20260313_215724`:
*   **`results.csv`**: Detailed metrics for all individuals and generations.
*   **`best_*.json`**: The best architecture found for each dataset.
*   **`program_db.jsonl`**: Historical log of all generated solutions.

## 📄 License & Citation

This project is part of academic research. Please refer to the `LICENSE` file for details.

### Citation
*Paper title and DOI to be added upon publication.*
> **José Daniel Narváez Flores** (2025). ArchiGenMS: Generative AI and Formal Verification in Microservice Discovery.

---
*Para la versión en español, consulta [README_es.md](README_es.md).*
