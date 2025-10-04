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
- [Object Model](https://lucid.app/lucidspark/909c5e71-6f4f-48bc-9d06-a3bad973050d/edit?viewport_loc=-3782%2C-1223%2C2908%2C2008%2C0_0&invitationId=inv_06a89c08-fede-44a0-9ebf-8822f3c9a18e)
- Describe all invariants that are not explicitly mentioned in the given specification but were discovered during the modeling process.
  - The spec mentions "each rider may have at most one active ride request", but additional predicate `driverServingConsistency` were needed to disallow same driver from being associated to the multiple riders
  - The spec does not specifically mention this, but we need predicate `domainsWellFormed` to prevent relationships between non-existent entities.
  - The spec does not specifically mention this, but we have added predicate `originDestSane` to prevent same origin and destination.
- Describe how you validated your model to ensure that you did not miss any important invariants. If possible, refer to the test predicates that you have developed during the modeling process.
  - We used test cases as well visualized sample runs to validate our model. Specific test cases such as `test_AvailableDriverIsAssigned` and `test_CompletedRequestIsAssigned` helped us find cases were the predicates were under-specified.
- List the scopes used for checking the assertions for invariant preservation. Why did you choose these scopes, and why do you think they are sufficient?
  - The scopes for checking the invariant preservation assertions in the final Alloy model were as follows:
      - requestPreservesInv: check requestPreservesInv for 6 but exactly 1 State, 6 seq
      - cancelPreservesInv: check cancelPreservesInv for 7 but exactly 1 State, 6 seq
      - matchPreservesInv: check matchPreservesInv for 7 but exactly 1 State, 6 seq
      - completePreservesInv: check completePreservesInv for 7 but exactly 1 State, 6 seq
  - We felt that that scope of 6 or 7 provides enough atoms(?) to cover most of the interesting interactions.


- `fsp/presto.fsp`  
  FSP model of the scheduler:  
  - to be done
  - 
  - 


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
## Reflection
1. What are the strengths of Alloy that make it suitable for Task 1? What are its weaknesses?
2. What are the strengths of FSP that make it suitable for Task 2? What are its weaknesses?
3. What other aspects (not covered in this project) of a ride sharing app like Presto would be difficult to model using Alloy or FSP? Why so?
---

## 👥 Team Members
- Iris Huang – Alloy modeling & validation testing 
- Viren Dodia – Alloy modeling & validation   
- Ray Xue – FSP modeling & verification  
- Ziqin Shen – FSP modeling & verification   

---


