VENV = .venv
PIP = $(VENV)/bin/pip
PROJ = src

.PHONY: help clean ftm lint-flake8 lint-mypy

help:
	@echo "Usage:"
	@echo "    make setup        =>  create virtual environment and install dependencies"
	@echo "    make clean        =>  remove .venv, __pycache__, .mypy_cache"
	@echo "    make fmt          =>  format the project with black"
	@echo "    make lint-flake8  =>  lint the project with flake8"
	@echo "    make lint-mypy    =>  lint the project with mypy"

setup: requirements.txt
	python3 -m venv $(VENV)
	$(PIP) install -r requirements.txt

clean:
	rm -rf $(VENV)
	rm -rf `find . -type d -name __pycache__ -or -name .mypy_cache`

fmt:
	black --target-version py310 $(PROJ)

lint-flake8:
	flake8 --max-line-length=88 $(PROJ)

lint-mypy:
	mypy --follow-imports=silent --ignore-missing-imports --show-column-numbers --no-pretty --strict $(PROJ)
