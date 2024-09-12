type tBallot = int;
type tValue = int;
type tBVPair = (ballot: tBallot, value: tValue);

pure MkPair(b: tBallot, v: tValue): tBVPair = (ballot=b, value=v);

type tPrepare = (proposer: machine, acceptor: machine, ballot: tBallot);
type tPromise = (acceptor: machine, promised: tBallot, prev: tBallot, accepted: tValue);
type tPropose = (proposer: machine, ballot: tBallot, value: tValue);
type tAccept = (acceptor: machine, ballot: tBallot, value: tValue);
type tDecide = (proposer: machine, ballot: tBallot, value: tValue);

event eP1A: tPrepare;
event eP1B: tPromise;
event eP2A: tPropose;
event eP2B: tAccept;
event eDecide: tDecide;

machine Proposer {
    var ballot: tBallot;
    var value: tValue;
    var highestBallot: tBallot;

    var p1bReceived: set[machine];
    var p2bReceived: set[machine];

    start state Prepare {
        entry {
            var acceptor: machine;
            foreach (acceptor in acceptors())
            invariant forall new (e: event) :: e is eP1A;
            invariant forall new (e: event) :: forall (m: machine) :: e targets m ==> m in acceptors();
            invariant forall new (e: eP1A) :: e.ballot == ballot && e.proposer == this;
            {
                send acceptor, eP1A, (proposer=this, acceptor=acceptor, ballot=ballot);
            }
        }

        on eP1B do (payload: tPromise) {
            var acceptor: machine;
            if (payload.prev > highestBallot) {
                assert payload.prev != nullBallot();
                assert payload.accepted != nullValue();
                highestBallot = payload.prev;
                value = payload.accepted;
            }
            assert highestBallot >= payload.prev;
            // p1bReceived += (payload.acceptor);
            assume payload.acceptor in p1bReceived;
            if (isQuorum(p1bReceived)) {
                foreach (acceptor in acceptors())
                invariant forall new (e: event) :: e is eP2A;
                invariant forall new (e: event) :: forall (m: machine) :: e targets m ==> m in acceptors();
                invariant forall new (e: eP2A) :: e.ballot == ballot && e.value == value && e.proposer == this;
                {
                    send acceptor, eP2A, (proposer=this, ballot=ballot, value=value);
                }
                goto Proposing;
            }
        }
        ignore eP1A, eP2A, eP2B, eDecide;
    }

    state Proposing {
        on eP2B do (payload: tAccept) {
            // p2bReceived += (payload.acceptor);
            assume payload.acceptor in p2bReceived;
            if (isQuorum(p2bReceived)) {
                send this, eDecide, (proposer=this, ballot=payload.ballot, value=payload.value);
                goto Done;
            }
        }
        ignore eP1A, eP1B, eP2A, eDecide;
    }
    state Done {
        ignore eP1A, eP1B, eP2A, eP2B, eDecide;
    }
}

machine Acceptor {
    var promised: tBallot;
    var prevBallot: tBallot;
    var prevValue: tValue;

    start state NotAccepted {
        on eP1A do (payload: tPrepare) {
            if (payload.ballot > promised) {
                promised = payload.ballot;
                send payload.proposer, eP1B, (acceptor=this, promised=promised, prev=prevBallot, accepted=prevValue);
            }
        }

        on eP2A do (payload: tPropose) {
            if (payload.ballot >= promised) {
                promised = payload.ballot;
                prevBallot = payload.ballot;
                prevValue = payload.value;
                send payload.proposer, eP2B, (acceptor=this, ballot=payload.ballot, value=payload.value);
            }
        }
        ignore eDecide, eP1B, eP2B;
    }
}

pure acceptors(): set[machine];
pure proposers(): set[machine];
pure nullBallot(): tBallot;
pure nullValue(): tValue;
// Some facts about null ballot and null value
axiom forall (b: tBallot) :: b != nullBallot() ==> b > nullBallot();
axiom forall (p1: Proposer, p2: Proposer) :: (p1 == p2) == (p1.ballot == p2.ballot);
init forall (x: Proposer) :: x.ballot > nullBallot();
invariant proposer_ballot_valid: forall (x: Proposer) :: x.ballot > nullBallot();
init forall (x: Proposer) :: x.value != nullValue();
invariant proposer_value_valid: forall (x: Proposer) :: x.value != nullValue();

// constant set of proposers and acceptors
axiom exists (x: machine) :: x in acceptors();
init forall (a: machine) :: a in acceptors() == a is Acceptor;
invariant acceptors_const: forall (a: machine) :: a in acceptors() == a is Acceptor;
init forall (p: machine) :: p in proposers() == p is Proposer;
invariant proposers_const: forall (p: machine) :: p in proposers() == p is Proposer;

// look up proposer with the ballot
pure proposerOf(b: tBallot): machine;
axiom forall (p: Proposer, b: tBallot) :: (p.ballot == b) == (proposerOf(b) == p);
pure hasBallot(m: machine, b: tBallot): bool = proposerOf(b) == m;

// Definition of quorums
pure isSubset(s1: set[machine], s2: set[machine]): bool = forall (x: machine) :: x in s1 ==> x in s2;
pure isQuorum(s: set[machine]): bool;
init forall (s: set[machine]) :: isQuorum(s) ==> isSubset(s, acceptors());
invariant quorum_of_acceptors: forall (s: set[machine]) :: isQuorum(s) ==> isSubset(s, acceptors());
init forall (s1: set[machine], s2: set[machine]) ::
        isQuorum(s1) && isQuorum(s2) ==> exists (x: machine) :: x in s1 && x in s2;
invariant quorum_def: forall (s1: set[machine], s2: set[machine]) ::
        isQuorum(s1) && isQuorum(s2) ==> exists (x: machine) :: x in s1 && x in s2;

// initial states
init forall (p: Proposer) :: p.highestBallot == nullBallot() &&
                             p.p1bReceived == default(set[machine]) &&
                             p.p2bReceived == default(set[machine]);
init forall (a: Acceptor) :: a.promised == nullBallot() &&
                             a.prevBallot == nullBallot() &&
                             a.prevValue == nullValue();
invariant proposer_has_ballot: forall (p: Proposer) :: hasBallot(p, p.ballot);

// Debug use
init forall (p1: machine, p2: machine) :: p1 in proposers() && p2 in proposers() ==> p1 == p2;
invariant debug: forall (p1: machine, p2: machine) :: p1 in proposers() && p2 in proposers() ==> p1 == p2;

// Safety
// This failed
// invariant one_value_decided: forall (x: eDecide, y: eDecide) :: sent x && sent y ==> x.value == y.value;
invariant one_value_decided: forall (x: eDecide, y: eDecide) :: sent x && sent y ==> x.proposer in proposers() && y.proposer in proposers() && x.proposer == y.proposer && x.value == y.value;

// Aux
// invariant decided_by_quorum: forall (e: eDecide, p: Proposer) :: sent e && e.proposer == p ==> isQuorum(p.p2bReceived) && forall (a: Acceptor) :: a in p.p2bReceived ==> a.prevValue == e.value;
// invariant propose_decision: forall (e1: eDecide, e2: eP2A) :: sent e1 && sent e2 && e2.ballot >= e1.ballot ==> e2.value == e1.value;

/* Facts about events*/
// eP1A
invariant p1a_targets_acceptors: forall (e: eP1A, m: machine) :: e targets m && !(m in acceptors()) ==> !inflight e;
invariant p1a_sent_by_proposers: forall (e: eP1A, m: machine) :: e.proposer == m && !(m in proposers()) ==> !inflight e;
invariant p1a_ballot_correct:    forall (e: eP1A) :: inflight e ==> hasBallot(e.proposer, e.ballot);

// eP1B
invariant p1b_targets_proposers: forall (e: eP1B, m: machine) :: e targets m && !(m in proposers()) ==> !inflight e;
invariant p1b_sent_by_acceptors: forall (e: eP1B, m: machine) :: e.acceptor == m && !(m in acceptors()) ==> !inflight e;
invariant p1b_updates_promise: forall (e: eP1B, a: Acceptor) :: inflight e && e.acceptor == a ==> e.promised <= a.promised;
invariant p1b_prev_round:      forall (e: eP1B) :: inflight e ==> e.promised > e.prev;
invariant p1b_may_has_accepted:forall (e: eP1B) :: sent e ==> (e.prev == nullBallot()) == (e.accepted == nullValue());
// Failed to prove
// invariant p1b_received_means_sent: forall (p: Proposer, e: eP1B, a: machine) ::
//                                                    a in p.p1bReceived && e.acceptor == a ==> sent e;

// eP2A
invariant p2a_targets_acceptors: forall (e: eP2A, m: machine) :: e targets m && !(m in acceptors()) ==> !inflight e;
invariant p2a_sent_by_proposers: forall (e: eP2A, m: machine) :: e.proposer == m && !(m in proposers()) ==> !inflight e;
invariant p2a_sent_not_in_prepare: forall (e: eP2A, m: Proposer) :: sent e && e.proposer == m ==> !(m is Prepare);
invariant p2a_valid_values:      forall (e: eP2A, p: Proposer) :: sent e && e.proposer == p ==> e.ballot == p.ballot && e.value == p.value && e.ballot > nullBallot() && e.value != nullValue();

// eP2B
invariant p2b_targets_proposers: forall (e: eP2B, m: machine) :: e targets m && !(m in proposers()) ==> !inflight e;
invariant p2b_sent_by_acceptors: forall (e: eP2B, m: machine) :: e.acceptor == m && !(m in acceptors()) ==> !inflight e;
invariant p2b_updates_promise:   forall (e: eP2B, a: Acceptor) :: inflight e && e.acceptor == a ==> e.ballot <= a.promised;
invariant p2b_means_proposing:   forall (e: eP2B, p: Proposer) :: sent e && e targets p ==> !(p is Prepare);
invariant p2b_valid_values:      forall (e1: eP2B, p: Proposer) :: sent e1 && e1 targets p ==> e1.ballot == p.ballot && e1.value == p.value;

// eDecide
invariant decided_from_proposer: forall (e: eDecide) :: inflight e ==> e.proposer in proposers();
invariant decision_valid: forall (e: eDecide, p: Proposer) :: inflight e && e.proposer == p ==> e.ballot == p.ballot && e.value == p.value;
invariant done_after_decision: forall (e: eDecide, p: Proposer) :: sent e && e.proposer == p ==> p is Done;

// Acceptor states
invariant promised_ge_accepted: forall (a: Acceptor) :: a.promised >= a.prevBallot;
invariant value_ballot_pair: forall (a: Acceptor) :: (a.prevBallot == nullBallot()) == (a.prevValue == nullValue());
