// Presto — Alloy structural model with FCFS queue (built-in `seq`)
// Matches the spec: riders/drivers/requests, operations, invariants, FCFS queue.

//--------------------------------------
// Basic entities & enums
//--------------------------------------
sig Rider {}
sig Driver {}
sig Request {}
sig Location {}

abstract sig DStatus {}
one sig Available, Driving, Offline extends DStatus {}

abstract sig RqStatus {}
one sig Pending, Riding, Completed, Cancelled extends RqStatus {}

//--------------------------------------
// System state (snapshot style)
//--------------------------------------
sig State {
  // Universe (which atoms this snapshot is aware of)
  riders:   set Rider,
  drivers:  set Driver,
  requests: set Request,

  // Request fields
  reqRider:     Request -> one Rider,
  origin:       Request -> one Location,
  destination:  Request -> one Location,
  reqStatus:    Request -> one RqStatus,
  assignedTo:   Request -> lone Driver,     // driver assigned while Riding

  // Driver fields
  dStatus: Driver -> one DStatus,
  regions: Driver -> set Location,          // locations this driver serves

  // FCFS queue of *exactly* the Pending requests, in arrival order
  pendingQ: seq Request
}

//--------------------------------------
// Helper predicates (invariants building blocks)
//--------------------------------------

// Queue contains exactly the pending requests, no duplicates, full coverage
pred queueWellFormed[s1: State] {
  let q = s1.pendingQ.elems |
    q = { rq: s1.requests | s1.reqStatus[rq] = Pending } and
    all rq: s1.requests | (s1.reqStatus[rq] = Pending) iff (rq in q)
  // (Because it's a sequence of a set, this implies no duplicates.)
}

// Each Rider has at most one "active" request (Pending or Riding)
pred oneActivePerRider[s1: State] {
  all r: Rider |
    lone { rq: s1.requests | s1.reqRider[rq] = r and s1.reqStatus[rq] in (Pending + Riding) }
}

// A Driver serves at most one request; Driving iff serving one
pred driverServingConsistency[s1: State] {
  all d: Driver |
    lone { rq: s1.requests | s1.assignedTo[rq] = d } and
    ((some rq: s1.requests | s1.assignedTo[rq] = d) iff s1.dStatus[d] = Driving)
}

// Status/assignment consistency for each Request
pred assignmentStatusConsistency[s1: State] {
  all rq: s1.requests |
    (s1.reqStatus[rq] = Riding)    implies one s1.assignedTo[rq] and
    (s1.reqStatus[rq] = Pending)   implies no  s1.assignedTo[rq] and
    (s1.reqStatus[rq] in (Completed + Cancelled)) implies no s1.assignedTo[rq]
}

// Optional sanity: start and end differ (drop if you want to allow equal)
pred originDestSane[s1: State] { all rq: s1.requests | s1.origin[rq] != s1.destination[rq] }

//--------------------------------------
// Global invariants
//--------------------------------------
pred inv[s1: State] {
  queueWellFormed[s1]
  oneActivePerRider[s1]
  driverServingConsistency[s1]
  assignmentStatusConsistency[s1]
  originDestSane[s1]
}

//--------------------------------------
// Frame helpers
//--------------------------------------
pred unchangedUniverse[s1, s2: State] {
  s1.riders = s2.riders and s1.drivers = s2.drivers and s1.requests = s2.requests
}

//--------------------------------------
// Operations
//--------------------------------------

// request(r, rq, o, d): rider r creates a fresh Pending request rq at the tail of the queue
pred request[s1, s2: State, r: Rider, rq: Request, o, d: Location] {
  inv[s1]
  r in s1.riders and
  rq not in s1.requests and
  // r must have no active request already
  no { q: s1.requests | s1.reqRider[q] = r and s1.reqStatus[q] in (Pending + Riding) }

  // Universe grows by rq
  s2.riders   = s1.riders
  s2.drivers  = s1.drivers
  s2.requests = s1.requests + rq

  // Copy driver meta
  s2.dStatus = s1.dStatus
  s2.regions = s1.regions
  s2.assignedTo = s1.assignedTo        // rq not yet in domain

  // Copy request fields for existing requests
  (s2.reqRider     - rq->Rider)    = s1.reqRider
  (s2.origin       - rq->Location) = s1.origin
  (s2.destination  - rq->Location) = s1.destination
  (s2.reqStatus    - rq->RqStatus) = s1.reqStatus

  // Set fields for the new request
  s2.reqRider    = s2.reqRider    + rq->r
  s2.origin      = s2.origin      + rq->o
  s2.destination = s2.destination + rq->d
  s2.reqStatus   = s2.reqStatus   ++ (rq->Pending)
  no s2.assignedTo[rq]

  // Enqueue at tail
  s2.pendingQ = s1.pendingQ.add[rq]

  inv[s2]
}

// cancel(r): rider r cancels their pending request; remove it from the queue
pred cancel[s1, s2: State, r: Rider] {
  inv[s1]
  r in s1.riders

  // Bind the unique pending request rq of r and its index i in the queue
  one rq: s1.requests, i: s1.pendingQ.idxOf[rq] |
    s1.reqRider[rq] = r and s1.reqStatus[rq] = Pending and

    // Universe unchanged
    unchangedUniverse[s1, s2] and

    // Driver meta unchanged
    s2.dStatus    = s1.dStatus and
    s2.regions    = s1.regions and
    s2.assignedTo = s1.assignedTo and   // rq has no assignment by invariant

    // Request fields unchanged except rq.status
    s2.reqRider    = s1.reqRider and
    s2.origin      = s1.origin and
    s2.destination = s1.destination and
    s2.reqStatus   = (s1.reqStatus - rq->RqStatus) ++ (rq->Cancelled) and

    // Remove rq from queue by its index i
    s2.pendingQ    = s1.pendingQ.delete[i]

  inv[s2]
}



// match(r, d): assign the *head* request (belonging to r) to available driver d
pred match[s1, s2: State, r: Rider, d: Driver] {
  inv[s1]
  r in s1.riders and d in s1.drivers and s1.dStatus[d] = Available
  #s1.pendingQ > 0

  let rq = s1.pendingQ.first | {
    // rq preconditions + region rule
    s1.reqRider[rq] = r and
    s1.reqStatus[rq] = Pending and
    (
      (s1.origin[rq] in s1.regions[d] and s1.destination[rq] in s1.regions[d])
      or
      no d2: Driver |
        s1.dStatus[d2] = Available and
        s1.origin[rq] in s1.regions[d2] and
        s1.destination[rq] in s1.regions[d2]
    ) and

    // Universe unchanged
    unchangedUniverse[s1, s2] and

    // Update assignment and statuses (rq is in scope here)
    s2.assignedTo = s1.assignedTo + rq->d and
    s2.reqStatus  = (s1.reqStatus - rq->RqStatus) ++ (rq->Riding) and
    s2.dStatus    = (s1.dStatus - d->DStatus)     ++ (d->Driving) and

    // Copy-through fields
    s2.reqRider    = s1.reqRider and
    s2.origin      = s1.origin and
    s2.destination = s1.destination and
    s2.regions     = s1.regions and

    // Dequeue head
    s2.pendingQ    = s1.pendingQ.rest and

    // Post
    inv[s2]
  }
}



// complete(r, d): finish the riding request between r and d
pred complete[s1, s2: State, r: Rider, d: Driver] {
  inv[s1]
  r in s1.riders and d in s1.drivers

  // Bind the unique riding request of r assigned to d, and keep all updates in this scope
  one rq: s1.requests | {
    s1.reqRider[rq] = r and
    s1.reqStatus[rq] = Riding and
    s1.assignedTo[rq] = d and

    // Universe unchanged
    unchangedUniverse[s1, s2] and

    // Complete the trip
    s2.reqStatus  = (s1.reqStatus - rq->RqStatus) ++ (rq->Completed) and
    s2.assignedTo = s1.assignedTo - rq->d and
    s2.dStatus    = (s1.dStatus - d->DStatus)     ++ (d->Available) and

    // Unchanged fields
    s2.reqRider    = s1.reqRider and
    s2.origin      = s1.origin and
    s2.destination = s1.destination and
    s2.regions     = s1.regions and
    s2.pendingQ    = s1.pendingQ and

    // Post
    inv[s2]
  }
}


//--------------------------------------
// Assertions: each op preserves invariants
//--------------------------------------
assert requestPreservesInv {
  all s1, s2: State, r: Rider, rq: Request, o, d: Location |
    request[s1, s2, r, rq, o, d] implies (inv[s1] and inv[s2])
}
check requestPreservesInv for 6 but exactly 1 State, 6 seq

assert cancelPreservesInv {
  all s1, s2: State, r: Rider |
    cancel[s1, s2, r] implies (inv[s1] and inv[s2])
}
check cancelPreservesInv for 7 but exactly 1 State, 6 seq

assert matchPreservesInv {
  all s1, s2: State, r: Rider, d: Driver |
    match[s1, s2, r, d] implies (inv[s1] and inv[s2])
}
check matchPreservesInv for 7 but exactly 1 State, 6 seq

assert completePreservesInv {
  all s1, s2: State, r: Rider, d: Driver |
    complete[s1, s2, r, d] implies (inv[s1] and inv[s2])
}
check completePreservesInv for 7 but exactly 1 State, 6 seq

//--------------------------------------
// Sample runs to visualize states
//--------------------------------------

// An empty, well-formed state (no requests)
pred emptyState[s1: State] {
  no s1.requests and no s1.pendingQ and all d: s1.drivers | s1.dStatus[d] != Driving
}
run { some s1: State | inv[s1] and emptyState[s1] } for 6 but exactly 1 State, 4 seq

// One pending request at head
pred onePendingAtHead[s1: State] {
  some s1.requests and some s1.riders and some s1.drivers
  #s1.pendingQ = 1
  let rq = s1.pendingQ.first |
    s1.reqStatus[rq] = Pending and one s1.reqRider[rq]
}
run { some s1: State | inv[s1] and onePendingAtHead[s1] } for 8 but exactly 1 State, 4 seq
