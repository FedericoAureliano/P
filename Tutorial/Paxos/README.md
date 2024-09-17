# Issues
## Relationship between exists a message sent and a buffer that holds the payload of the message
Consider the spec machine
```
spec Aux observes eP1B, eP2B, eP2A, eDecide {
    var decided: map[machine, tBVPair];
    start state S {
        on eDecide do (payload: tDecide) {
            decided[payload.proposer] = MkPair(payload.ballot, payload.value);
        }
    }
}
```
It seems that we have to prove
```
forall (b: tBallot, v: tValue, p: Proposer) :: p in Aux.decided && Aux.decided[p] == (b=b, v=v) ==> exists (e: eDecide) :: sent e && e.proposer == p && e.ballot == b && e.value == v;
```

## Checking individual handler failed but verifying all targets passed
Under the current commit,
> p compile --check-only eP1B -t 200
gets the result
```
Failed to verify 3 conditions.
  - Failed to verify assertion at PSrc/System.p:43:17 
  - Failed to verify invariant proposer_value_valid at PSrc/System.p:39:12 
  - Failed to verify invariant p2a_valid_values at PSrc/System.p:39:12
```
However running
> p compile -t 200
passes all verifications. 

## inflight ==> sent (not a bug)
When enabling debugging (only 1 proposer in the system), the invariant `forall (x: eDecide, y: eDecide) :: sent x && sent y ==> x.value == y.value` failed to check, but `forall (x: eDecide, y: eDecide) :: sent x && sent y ==> x.proposer in proposers() && y.proposer in proposers() && x.proposer == y.proposer && x.value == y.value` was verified without error. However, the additional clauses are implied by debugging setup and other invariants: 
```c++
// debug setup
init forall (p1: machine, p2: machine) :: p1 in proposers() && p2 in proposers() ==> p1 == p2;
invariant debug: forall (p1: machine, p2: machine) :: p1 in proposers() && p2 in proposers() ==> p1 == p2;

// facts about eDecide
invariant decided_from_proposer: forall (e: eDecide) :: inflight e ==> e.proposer in proposers();
invariant decision_valid: forall (e: eDecide, p: Proposer) :: inflight e && e.proposer == p ==> e.ballot == p.ballot && e.value == p.value;
```
*This is because inflight implies sent and therefore the invariant decided_from_proposer has a stronger pre-condition*

# Feature requests
- Option type: this will greatly simplify the proof! (currently nullBallot and nullValue makes a lot of things complicated).