# Fridge Compiler

## Overview

The Fridge Compiler is an SMT-based Python tool designed for synthesizing optimal Boolean circuits from a given molecular inventory. It is tailored for CRN-style molecular computing implementable through DNA Strand Displacement.

Unlike heuristic methods that may produce suboptimal circuits — or circuits for which you may not have the necessary parts — the Fridge Compiler guarantees logical soundness, completeness, and optimality based on user-specified constraints and cost functions. Additionally, it supports the synthesis of a unique class of cyclic molecular circuits, often resulting in smaller circuits.

## Table of Contents

- [Overview](#overview)
- [Installation](#installation)
- [Directory Structure](#directory-structure)
- [Usage](#usage)
  - [Run Tests to Reproduce Data](#run-tests-to-reproduce-data)
  - [Run Examples](#run-examples)
- [Data](#data)

## Installation

1. Clone the repository:
    ```
    git clone https://github.com/lwathieu1/fridge-compiler.git
    ```
2. Install the required packages:
    ```
    pip install -r python3_11_requirements.txt
    ```

## Directory Structure

```plaintext
/fridge-compiler
├─ /data  (Data used in paper)
├─ fridge_utils.py (Fridge compiler code)
├─ cmsb_results.py (Script to reproduce data in the paper)
├─ examples.ipynb (Jupyter notebook with simple examples)
├─ python3_11_requirements.txt (Python requirements)
└─ README.md (This file)
```

## Usage


### Run Examples
To understand basic usage and run simple test cases, open the Jupyter notebook `examples.ipynb`. This notebook provides code to run tests on specific 5-gate 12-wire and 3-gate complete cyclic circuits.

Open the notebook with:

```bash
jupyter notebook examples.ipynb
```

### Run Tests to Reproduce Data
To reproduce the data and figures presented in the paper, run the `cmsb_results.py` script. This script performs comprehensive tests on 3-gate and 4-gate acyclic and cyclic circuits, as well as additional tests on 19-gate 27-wire and 5-gate 12-wire configurations.

Run the script with:

```bash
python cmsb_results.py
```

## Data

The `/data` directory contains data sets used to populate tables and figures in the paper.
