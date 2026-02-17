# ArchiGenMS (Research Project)

**Repository Name**: `archi-ai`

ArchiGenMS es un proyecto de investigación que aprovecha la inteligencia artificial y la computación evolutiva para diseñar arquitecturas de microservicios automáticamente a partir de historias de usuario. El sistema utiliza **Lean 4** para la validación formal de las arquitecturas generadas, asegurando su corrección y calidad estructural.

## ✨ Características Principales

* **Diseño Automatizado de Arquitecturas**: Genera arquitecturas de microservicios a partir de historias de usuario en lenguaje natural.
* **Enfoque Evolutivo**: Implementa un algoritmo genético que explora el espacio de soluciones para encontrar diseños óptimos, guiado por métricas de calidad de software.
* **Integración con LLMs**: Utiliza modelos de lenguaje (como GPT-4o-mini) para interpretar requisitos y proponer candidatos iniciales y mutaciones.
* **Validación Formal**: Integra el asistente de pruebas **Lean 4** para validar matemáticamente la estructura y calcular métricas precisas (LCOM, SGM, Acoplamiento).

## 🛠️ Tecnologías Utilizadas

* **Lenguaje Principal**: Python 3.x
* **Validación Formal**: [Lean 4](https://leanprover.github.io/)
* **Inteligencia Artificial**: OpenAI API (`gpt-4o-mini`)
* **Librerías Clave**:
    * `numpy`, `networkx`, `nltk` (Análisis y Evolución)
    * `python-dotenv` (Gestión de configuración)

## 📂 Estructura del Proyecto

```
archi-ai/
├── data/
│   └── user-stories-datasets/  # Conjuntos de datos con historias de usuario (.txt)
├── python/
│   ├── experiments/            # Resultados: mejores arquitecturas (JSON) y métricas (CSV)
│   ├── formal/                 # Código Lean 4 para validación y métricas
│   │   ├── src/
│   │   │   ├── ValidateGenotype.lean
│   │   │   └── ServiceMetrics.lean
│   │   └── lakefile.lean       # Configuración del proyecto Lean
│   ├── src/
│   │   └── alpha_pipeline/     # Lógica del algoritmo evolutivo
│   │       └── runner.py       # Script principal de ejecución
│   └── requirements.txt        # Dependencias de Python
├── .env                        # Variables de entorno (API Keys)
└── README.md
```

## 🚀 Cómo Empezar

### Prerrequisitos

1.  **Python 3.9+**
2.  **Lean 4**: Instalado vía [elan](https://github.com/leanprover/elan).
3.  **OpenAI API Key**: Necesaria para el funcionamiento del LLM.

### Instalación

1.  **Clona el repositorio:**

    ```bash
    git clone https://github.com/tu_usuario/archi-ai.git
    cd archi-ai
    ```

2.  **Configura el entorno de Python:**

    ```bash
    python -m venv venv
    source venv/bin/activate  # En Windows: venv\Scripts\activate
    pip install -r python/requirements.txt
    ```

3.  **Compila el proyecto Lean:**
    Es necesario compilar el validador formal antes de ejecutar el pipeline.

    ```bash
    cd python/formal
    lake build
    cd ../..
    ```

4.  **Configura las variables de entorno:**
    Crea un archivo `.env` en la raíz del proyecto:

    ```bash
    OPENAI_API_KEY='tu_clave_de_api_aqui'
    ```

## 🏃‍♂️ Cómo Usarlo

Para ejecutar el pipeline evolutivo y generar una arquitectura para un conjunto de historias de usuario específico:

```bash
python python/src/alpha_pipeline/runner.py
```
*Nota: Actualmente el script `runner.py` procesa automáticamente todos los archivos `.txt` en `data/user-stories-datasets`. Puedes modificar el `main` en `runner.py` si deseas ejecutar uno específico.*

### Resultados
Los resultados se guardan en `python/experiments`:
* **`results.csv`**: Métricas detalladas de todos los individuos y generaciones.
* **`best_*.json`**: La mejor arquitectura encontrada para cada dataset.
* **`program_db.jsonl`**: Registro histórico de todas las soluciones generadas.

## 📄 Licencia

Este proyecto es parte de una investigación académica. Consulta el archivo `LICENSE` para más detalles.