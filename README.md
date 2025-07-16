Claro, aquí tienes una propuesta completa para el archivo `README.md` del proyecto `archi-ai`. Está basada en el análisis del código y la estructura del repositorio.

-----

# archi-ai

`archi-ai` es un proyecto innovador que aprovecha la inteligencia artificial para diseñar arquitecturas de microservicios a partir de historias de usuario. Utiliza un enfoque de computación evolutiva para generar y optimizar las arquitecturas, y emplea validación formal con el asistente de pruebas Lean para garantizar su correctitud.

## ✨ Características Principales

* **Diseño Automatizado de Arquitecturas**: Genera arquitecturas de microservicios de forma automática a partir de un conjunto de historias de usuario.
* **Enfoque Evolutivo**: Utiliza algoritmos evolutivos para explorar el espacio de soluciones y encontrar arquitecturas óptimas.
* **Integración con Modelos de Lenguaje**: Emplea modelos de lenguaje de OpenAI para interpretar las historias de usuario y asistir en la generación de la arquitectura.
* **Validación Formal**: Integra el asistente de pruebas Lean para validar formalmente los modelos de microservicios generados, asegurando su coherencia y robustez.
* **Análisis de Métricas**: Calcula diversas métricas de calidad de software como el acoplamiento y la cohesión (LCOM) para evaluar las arquitecturas generadas.

## 🛠️ Tecnologías Utilizadas

* **Lenguaje Principal**: Python 3.x
* **Computación Evolutiva y Análisis**:
    * `numpy`
    * `networkx`
    * `nltk`
* **Inteligencia Artificial**:
    * `openai`
* **Validación Formal**:
    * [Lean 4](https://leanprover.github.io/)
* **Herramientas de Desarrollo**:
    * `pytest` para pruebas.
    * `flake8` para linting.
    * `mypy` para chequeo de tipos estáticos.
    * `python-dotenv` para la gestión de variables de entorno.
* **CI/CD**:
    * GitHub Actions

## 📂 Estructura del Proyecto

```
archi-ai/
├── .github/
│   └── workflows/          # Workflows de Integración Continua para GitHub Actions
├── data/                   # Conjuntos de datos con historias de usuario (.txt)
├── python/
│   ├── experiments/        # Resultados de los experimentos (JSON y CSV)
│   ├── formal/             # Código de Lean para la validación formal
│   ├── src/                # Código fuente del pipeline evolutivo en Python
│   │   └── runner.py       # Punto de entrada para ejecutar los experimentos
│   ├── requirements.txt    # Dependencias de Python
│   └── ...
├── .gitignore
└── README.md
```

## 🚀 Cómo Empezar

Sigue estos pasos para configurar el entorno y ejecutar el proyecto.

### Prerrequisitos

* Python 3.9 o superior
* [elan](https://www.google.com/search?q=https://leanprover.github.io/lean4/doc/setup.html), el gestor de toolchains de Lean.

### Instalación

1.  **Clona el repositorio:**

    ```bash
    git clone https://github.com/tu_usuario/archi-ai.git
    cd archi-ai
    ```

2.  **Configura el entorno de Python:**
    Se recomienda usar un entorno virtual.

    ```bash
    python -m venv venv
    source venv/bin/activate  # En Windows: venv\Scripts\activate
    ```

3.  **Instala las dependencias de Python:**

    ```bash
    pip install -r python/requirements.txt
    ```

4.  **Configura el toolchain de Lean:**
    Navega al directorio de Lean y `elan` se encargará de instalar la versión correcta especificada en `lean-toolchain`.

    ```bash
    cd python/formal
    lake build
    cd ../..
    ```

5.  **Configura tus variables de entorno:**
    Crea un archivo `.env` en el directorio raíz del proyecto y añade tu clave de API de OpenAI.

    ```
    OPENAI_API_KEY='tu_clave_de_api_aqui'
    ```

## 🏃‍♂️ Cómo Usarlo

Para ejecutar el pipeline evolutivo y generar una arquitectura de microservicios a partir de un conjunto de historias de usuario, utiliza el script `runner.py`.

```bash
python python/src/runner.py --story_file data/g02-federalspending.txt
```

* El argumento `--story_file` especifica el archivo de historias de usuario a utilizar.
* Los resultados, incluyendo la mejor arquitectura en formato JSON y las métricas de la ejecución, se guardarán en la carpeta `python/experiments`.

## ⚙️ Workflows de CI/CD

El proyecto utiliza GitHub Actions para la automatización:

* **`lean_action_ci.yml`**: Se activa con cada `push` o `pull request`. Construye y prueba el código de Lean para asegurar que la lógica de validación formal es correcta.
* **`update.yml`**: Permite la actualización manual o programada de las dependencias de Lean.
* **`create-release.yml`**: Automatiza la creación de un nuevo *release* en GitHub cuando la versión del `lean-toolchain` es actualizada.

## 🤝 Contribuciones

Las contribuciones son bienvenidas. Si deseas colaborar, por favor sigue estos pasos:

1.  Haz un *fork* del repositorio.
2.  Crea una nueva rama para tu funcionalidad (`git checkout -b feature/nueva-funcionalidad`).
3.  Haz tus cambios y haz *commit* (`git commit -am 'Añade nueva funcionalidad'`).
4.  Haz *push* a tu rama (`git push origin feature/nueva-funcionalidad`).
5.  Crea un nuevo *Pull Request*.

## 📄 Licencia

Este proyecto está bajo la Licencia MIT. Consulta el archivo `LICENSE` para más detalles.

-----