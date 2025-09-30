# Presto Ride-Sharing App

This repository contains our team’s deliverables for the **CMU 17-614 Formal Methods Final Project**.  
We modeled *Presto*, a ride-sharing application similar to Uber/Lyft, using Alloy and FSP to analyze its correctness and reliability.

---

## 📌 Project Overview
Presto allows riders to make ride requests, drivers to accept rides, and the system to match them. The system state includes:
- Riders, Drivers, and Requests.
- Operations: `request`, `cancel`, `match`, `complete`:contentReference[oaicite:1]{index=1}.
- A **first-come, first-served (FCFS)** matching policy for fairness.

Our project models these aspects with:
- **Alloy** → structural model (state, invariants, operations, assertions).
- **FSP (LTSA)** → concurrency model (match-making protocol, property verification).

The report combines both models and reflects on their strengths and weaknesses.

---

## 📂 Repository Layout
- `alloy/presto.als`  
  Alloy model of Presto:  
  - Signatures (`Rider`, `Driver`, `Request`, etc.)  
  - Invariants (`inv`) ensuring constraints on requests, drivers, and queue  
  - Operations: `request`, `cancel`, `match`, `complete`  
  - Assertions verifying invariants are preserved  
  - Sample `run` commands for visualization

- `fsp/presto.fsp`  
  FSP model of the scheduler:  
  - 
  - 
  - 


- `report/project-report.tex` (with `project-report.pdf`)  
  Formal report answering required questions:  
  - Object Model Diagram (Alloy)  
  - Process Structure Diagram (FSP)  
  - Additional invariants discovered  
  - Validation strategy and scopes used  
  - Reflection: Alloy vs. FSP

- `README.md`  
  You are here: description of files and execution instructions.

---

## How to Execute the Models

### Alloy
1. Open `alloy/presto.als` in the [Alloy Analyzer](http://alloytools.org/).
2. ## to de done ##

### FSP / LTSA
1. Open `fsp/presto.fsp` in the [LTSA tool](http://www.doc.ic.ac.uk/ltsa/).
2. ## to de done ##

---

## 👥 Team Members
- Iris Huang – Alloy modeling & validation testing 
- Viren Dodia – Alloy modeling & validation   
- Ray Xue – FSP modeling & verification  
- Ziqin Shen – FSP modeling & verification   

---


