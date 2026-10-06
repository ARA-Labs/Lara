---
title: "All-in-one simulation-based inference"
authors: ["Manuel Gloeckler", "Michael Deistler", "Christian Weilbach", "Frank Wood", "Jakob H. Macke"]
year: 2024
venue: "Proceedings of the 41st International Conference on Machine Learning (ICML), PMLR 235"
doi: "arXiv:2404.09636v3"
ara_version: "1.0"
domain: "Simulation-Based Inference, Probabilistic Machine Learning"
keywords: ["simulation-based inference", "amortized Bayesian inference", "diffusion models", "transformers", "score matching", "arbitrary conditionals", "function-valued parameters", "attention masks", "posterior estimation", "scientific simulators"]
claims_summary:
  - "Simformer outperforms NPE on benchmark posterior approximation tasks and requires ~10x fewer simulations"
  - "Simformer can sample all arbitrary conditionals of the joint distribution (posterior, likelihood, parameter conditionals) from a single trained model"
  - "Simformer handles unstructured/missing data, infinite-dimensional (function-valued) parameters, and interval conditioning via guided diffusion"
abstract: >-
  Amortized Bayesian inference trains neural networks to solve stochastic
  inference problems using model simulations, thereby making it possible to
  rapidly perform Bayesian inference for any newly observed data. However,
  current simulation-based amortized inference methods are simulation-hungry
  and inflexible: They require the specification of a fixed parametric prior,
  simulator, and inference tasks ahead of time. Here, we present a new
  amortized inference method - the Simformer - which overcomes these
  limitations. By training a probabilistic diffusion model with transformer
  architectures, the Simformer outperforms current state-of-the-art amortized
  inference approaches on benchmark tasks and is substantially more flexible:
  It can be applied to models with function-valued parameters, it can handle
  inference scenarios with missing or unstructured data, and it can sample
  arbitrary conditionals of the joint distribution of parameters and data,
  including both posterior and likelihood. We showcase the performance and
  flexibility of the Simformer on simulators from ecology, epidemiology, and
  neuroscience, and demonstrate that it opens up new possibilities and
  application domains for amortized Bayesian inference on simulation-based
  models.
---

# All-in-one simulation-based inference

## Overview

This paper introduces the **Simformer**, a new method for amortized simulation-based inference (SBI) that combines probabilistic diffusion models with transformer architectures. Unlike previous SBI methods that require a fixed prior, simulator, and inference task (posterior OR likelihood), the Simformer trains on the joint distribution p(θ, x) and can sample arbitrary conditionals from a single trained model. The key architectural innovation is a tokenizer that encodes each variable (parameter or data) as a triple (identifier, value, condition state), processed by a transformer whose attention mask can encode known dependency structures. The score-based diffusion model then generates samples from any desired conditional by conditioning observed variables and reverse-diffusing unobserved ones. Guided diffusion enables conditioning on intervals rather than exact values.

The Simformer outperforms NPE on standard benchmark tasks while requiring approximately 10× fewer simulations, handles function-valued (∞-dimensional) parameters via random Fourier embeddings, gracefully accommodates unstructured and missing data, and can incorporate domain knowledge through structured attention masks. Applications span ecology (Lotka-Volterra), epidemiology (SIRD with time-varying contact rate), and neuroscience (Hodgkin-Huxley with metabolic energy constraints).

## Layer Index

### Cognitive Layer (`/logic`)
| File | Description |
|------|-------------|
| [problem.md](logic/problem.md) | Observations → gaps → key insight motivating the Simformer |
| [claims.md](logic/claims.md) | 6 falsifiable claims (C01–C06) |
| [concepts.md](logic/concepts.md) | 10 key terms with formal definitions |
| [experiments.md](logic/experiments.md) | 6 verification plans (E01–E06) |
| [solution/architecture.md](logic/solution/architecture.md) | System design: Tokenizer → Transformer → Diffusion Score Model |
| [solution/algorithm.md](logic/solution/algorithm.md) | Denoising score matching + reverse SDE; general guidance Algorithm 1 |
| [solution/constraints.md](logic/solution/constraints.md) | Boundary conditions and known limitations |
| [solution/heuristics.md](logic/solution/heuristics.md) | 7 convergence and design heuristics |
| [related_work.md](logic/related_work.md) | 15 typed dependency entries |

### Physical Layer (`/src`)
| File | Description | Claims |
|------|-------------|--------|
| [execution/simformer.py](src/execution/simformer.py) | Tokenizer, score model, training loss, sampling | C01–C04 |
| [execution/sde.py](src/execution/sde.py) | VESDE/VPSDE drift, diffusion, perturbation kernel | C01, C02 |
| [execution/guided_diffusion.py](src/execution/guided_diffusion.py) | General guidance algorithm (Algorithm 1) | C05 |
| [execution/c2st.py](src/execution/c2st.py) | Classifier Two-Sample Test metric | C01–C03 |
| [configs/training.md](src/configs/training.md) | Training hyperparameters with rationale |  — |
| [configs/model.md](src/configs/model.md) | Transformer and SDE model configurations | — |
| [environment.md](src/environment.md) | Hardware, dependencies, seeds | — |

### Exploration Graph (`/trace`)
| File | Description |
|------|-------------|
| [exploration_tree.yaml](trace/exploration_tree.yaml) | 14-node research DAG (nested YAML) |

### Evidence (`/evidence`)
| File | Description |
|------|-------------|
| [README.md](evidence/README.md) | Full index of 4 tables + 6 figures |
| [tables/benchmark_c2st_posterior.md](evidence/tables/benchmark_c2st_posterior.md) | C2ST posterior accuracy across simulation budgets (Fig. 4a) |
| [tables/benchmark_c2st_all_cond.md](evidence/tables/benchmark_c2st_all_cond.md) | C2ST arbitrary conditionals across simulation budgets (Fig. 4b) |
| [tables/training_configs.md](evidence/tables/training_configs.md) | Exact model and SDE hyperparameters from Appendix A2.1 |
| [tables/sde_params.md](evidence/tables/sde_params.md) | VESDE and VPSDE parameter values |
| [figures/fig4a_benchmark_posterior.md](evidence/figures/fig4a_benchmark_posterior.md) | C2ST posterior curves: Simformer vs NPE across 4 tasks |
| [figures/fig4b_benchmark_all_cond.md](evidence/figures/fig4b_benchmark_all_cond.md) | C2ST all-conditionals curves: Simformer across Tree/HMM/TwoMoons/SLCP |
| [figures/fig_a7_eval_steps.md](evidence/figures/fig_a7_eval_steps.md) | C2ST vs evaluation steps for reverse SDE (50-step threshold) |
| [figures/fig_a5_extended_vesde.md](evidence/figures/fig_a5_extended_vesde.md) | Extended VESDE benchmark including NRE, NLE, NPSE |
| [figures/fig5c_lotka_volterra.md](evidence/figures/fig5c_lotka_volterra.md) | Lotka-Volterra C2ST for posterior and arbitrary conditionals |
| [figures/fig_a8_nll.md](evidence/figures/fig_a8_nll.md) | Average NLL for likelihood and posterior across benchmark tasks |
