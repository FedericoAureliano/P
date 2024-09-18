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

    var p1bReceived: map[machine, tBVPair];
    var p2bReceived: map[machine, tBVPair];

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
            // assert forall (a: machine) :: a in p1bReceived ==> p1bReceived[a].ballot <= highestBallot;
            p1bReceived[payload.acceptor] = MkPair(payload.prev, payload.accepted);
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
            p2bReceived[payload.acceptor] = MkPair(payload.ballot, payload.value);
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
    // var voted: set[tBVPair];

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
                // assume MkPair(payload.ballot, payload.value) in voted;
                send payload.proposer, eP2B, (acceptor=this, ballot=payload.ballot, value=payload.value);
            }
        }
        ignore eDecide, eP1B, eP2B;
    }
}

spec Aux observes eP1B, eP2B, eP2A, eDecide {
    var one_b_max: map[machine, set[(b1: tBallot, b2: tBallot, v: tValue)]];
    var voted: map[machine, set[tBVPair]];
    var proposed: map[machine, tBVPair];
    var decided: map[machine, tBVPair];
    start state S {
        on eP1B do (payload: tPromise) {
            if (!(payload.acceptor in one_b_max)) {
                one_b_max[payload.acceptor] = default(set[(b1: tBallot, b2: tBallot, v: tValue)]);
            }
            one_b_max[payload.acceptor] += ((b1=payload.promised, b2=payload.prev, v=payload.accepted));
        }

        on eP2B do (payload: tAccept) {
            if (!(payload.acceptor in voted)) {
                voted[payload.acceptor] = default(set[tBVPair]);
            }
            voted[payload.acceptor] += (MkPair(payload.ballot, payload.value));
        }

        on eP2A do (payload: tPropose) {
            proposed[payload.proposer] = MkPair(payload.ballot, payload.value);
        }

        on eDecide do (payload: tDecide) {
            decided[payload.proposer] = MkPair(payload.ballot, payload.value);
        }
    }
}

pure acceptors(): set[machine];
pure proposers(): set[machine];
pure nullBallot(): tBallot;
pure nullValue(): tValue;
// Some facts about null ballot and null value
init forall (b: tBallot) :: nullBallot() <= b;
invariant nb_unchanged: forall (b: tBallot) :: nullBallot() <= b;
invariant nb_ngt: forall (b1: tBallot, b2: tBallot) :: b1 > b2 ==> b1 != nullBallot();
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
pure isSubset(s1: map[machine, tBVPair], s2: set[machine]): bool = forall (x: machine) :: x in s1 ==> x in s2;
pure isQuorum(s: map[machine, tBVPair]): bool;
init forall (s: map[machine, tBVPair]) :: isQuorum(s) ==> isSubset(s, acceptors());
invariant quorum_of_acceptors: forall (s: map[machine, tBVPair]) :: isQuorum(s) ==> isSubset(s, acceptors());
init forall (s1: map[machine, tBVPair], s2: map[machine, tBVPair]) ::
        isQuorum(s1) && isQuorum(s2) ==> exists (x: machine) :: x in s1 && x in s2;
invariant quorum_def: forall (s1: map[machine, tBVPair], s2: map[machine, tBVPair]) ::
        isQuorum(s1) && isQuorum(s2) ==> exists (x: machine) :: x in s1 && x in s2;

// initial states
init forall (p: Proposer) :: p.highestBallot == nullBallot() &&
                             p.p1bReceived == default(map[machine, tBVPair]) &&
                             p.p2bReceived == default(map[machine, tBVPair]);
init forall (a: Acceptor) :: a.promised == nullBallot() &&
                             a.prevBallot == nullBallot() &&
                             a.prevValue == nullValue();
                            //  a.voted == default(set[tBVPair]);
init Aux.one_b_max == default(map[machine, set[(b1: tBallot, b2: tBallot, v: tValue)]]);
init Aux.voted == default(map[machine, set[tBVPair]]);
init Aux.proposed == default(map[machine, tBVPair]);
init Aux.decided == default(map[machine, tBVPair]);
invariant proposer_has_ballot: forall (p: Proposer) :: hasBallot(p, p.ballot);
invariant votes_are_acceptors: forall (p: Proposer, a: machine) :: a in p.p2bReceived ==> a in acceptors();
invariant promises_are_acceptors: forall (p: Proposer, a: machine) :: a in p.p1bReceived ==> a in acceptors();

pure one_b_max(a: machine, b1: tBallot, b2: tBallot, v: tValue): bool = a in Aux.one_b_max && (b1=b1, b2=b2, v=v) in Aux.one_b_max[a];
pure proposed(b: tBallot, v: tValue): bool = (proposerOf(b) in Aux.proposed) && Aux.proposed[proposerOf(b)] == MkPair(b, v);
pure voted(a: machine, b: tBallot, v: tValue): bool = a in Aux.voted && MkPair(b, v) in Aux.voted[a];
pure decided(b: tBallot, v: tValue): bool = proposerOf(b) in Aux.decided && Aux.decided[proposerOf(b)] == MkPair(b, v);

invariant acceptor_votes: forall (a: machine, b: tBallot, v: tValue) :: voted(a, b, v) ==> a in acceptors() && proposerOf(b) in proposers();
invariant acceptor_promise: forall (a: machine, b1: tBallot, b2: tBallot, v: tValue) :: one_b_max(a, b1, b2, v) ==> a in acceptors() && proposerOf(b1) in proposers();

// Relationships between predicates and event sent
invariant p1b_means_one_b_max: forall (e: eP1B) :: sent e ==> one_b_max(e.acceptor, e.promised, e.prev, e.accepted);
invariant one_b_max_means_sent: forall (a: machine, b1: tBallot, b2: tBallot, v: tValue) :: one_b_max(a, b1, b2, v) ==> exists (e: eP1B) :: sent e && e.acceptor == a && e.promised == b1 && e.prev == b2 && e.accepted == v;

invariant p2b_means_voting: forall (e: eP2B) :: sent e ==> voted(e.acceptor, e.ballot, e.value);
invariant voted_means_p2b:  forall (a: machine, b: tBallot, v: tValue) :: voted(a, b, v) ==> exists (e: eP2B) :: sent e && e.acceptor == a && e.ballot == b && e.value == v;

// invariant p2a_means_proposing: forall (e: eP2A) :: sent e ==> proposed(e.ballot, e.value);
// invariant proposed_means_p2a:  forall (b: tBallot, v: tValue) :: proposed(b, v) ==> exists (e: eP2A) :: sent e && e.ballot == b && e.value == v;

// Debug use
init forall (p1: machine, p2: machine) :: p1 in proposers() && p2 in proposers() ==> p1 == p2;
invariant debug: forall (p1: machine, p2: machine) :: p1 in proposers() && p2 in proposers() ==> p1 == p2;

// Safety
invariant one_value_decided: forall (x: eDecide, y: eDecide) :: sent x && sent y ==> x.value == y.value;

// Aux
invariant decided_by_quorum: forall (e: eDecide, p: Proposer) :: sent e && e.proposer == p ==> isQuorum(p.p2bReceived) && forall (a: machine) :: a in p.p2bReceived ==> voted(a, e.ballot, e.value);
invariant propose_decision: forall (e1: eDecide, e2: eP2A) :: sent e1 && sent e2 && e2.ballot >= e1.ballot ==> e1.value == e2.value;
invariant p1bReceived_means_one_b_max: forall (p: Proposer, a: machine) ::
                            a in p.p1bReceived ==> one_b_max(a, p.ballot, p.p1bReceived[a].ballot, p.p1bReceived[a].value);
invariant highest_ballot_running_max: forall (p: Proposer, a: machine) :: a in p.p1bReceived ==> p.highestBallot >= p.p1bReceived[a].ballot;

invariant p2bReceived_means_voted: forall (p: Proposer, a: machine) :: a in p.p2bReceived ==> voted(a, p.p2bReceived[a].ballot, p.p2bReceived[a].value);
invariant single_proposal_per_ballot: forall (e1: eP2A, e2: eP2A) :: sent e1 && sent e2 && e1.ballot == e2.ballot ==> e1.value == e2.value;

/* Facts about events*/
// eP1A
invariant p1a_targets_acceptors: forall (e: eP1A, m: machine) :: e targets m && !(m in acceptors()) ==> !sent e;
invariant p1a_sent_by_proposers: forall (e: eP1A, m: machine) :: e.proposer == m && !(m in proposers()) ==> !sent e;
invariant p1a_ballot_correct:    forall (e: eP1A) :: sent e ==> hasBallot(e.proposer, e.ballot);

// eP1B
invariant p1b_targets_proposers: forall (e: eP1B, m: machine) :: e targets m && !(m in proposers()) ==> !sent e;
invariant p1b_sent_by_acceptors: forall (e: eP1B, m: machine) :: e.acceptor == m && !(m in acceptors()) ==> !sent e;
invariant p1b_updates_promise: forall (e: eP1B, a: Acceptor) :: sent e && e.acceptor == a ==> e.promised <= a.promised;
invariant p1b_prev_round:      forall (e: eP1B) :: sent e ==> e.promised > e.prev;
invariant p1b_promise_ballot:  forall (e: eP1B, p: Proposer) :: sent e ==> (e targets p) == (e.promised == p.ballot);
invariant p1b_may_has_accepted:forall (e: eP1B) :: sent e ==> (e.prev == nullBallot()) == (e.accepted == nullValue());

// eP2A
invariant p2a_targets_acceptors:   forall (e: eP2A, m: machine) :: e targets m && !(m in acceptors()) ==> !(sent e);
invariant p2a_sent_by_proposers:   forall (e: eP2A) :: sent e ==> e.proposer in proposers();
invariant p2a_sent_not_in_prepare: forall (e: eP2A, m: Proposer) :: sent e && e.proposer == m ==> !(m is Prepare);
invariant p2a_valid_values:        forall (e: eP2A, p: Proposer) :: sent e && e.proposer == p ==> e.ballot == p.ballot && e.value == p.value && e.ballot > nullBallot() && e.value != nullValue();
invariant p2a_ballot_values:       forall (e: eP2A, p: Proposer) :: sent e ==> (e.proposer == p) == (e.ballot == p.ballot && e.value == p.value);

// eP2B
invariant p2b_targets_proposers: forall (e: eP2B, m: machine) :: e targets m && !(m in proposers()) ==> !sent e;
invariant p2b_sent_by_acceptors: forall (e: eP2B, m: machine) :: e.acceptor == m && !(m in acceptors()) ==> !sent e;
invariant p2b_updates_promise:   forall (e: eP2B, a: Acceptor) :: sent e && e.acceptor == a ==> e.ballot <= a.promised;
invariant p2b_means_proposing:   forall (e: eP2B, p: Proposer) :: sent e && e targets p ==> !(p is Prepare);
invariant p2b_valid_values:      forall (e1: eP2B, p: Proposer) :: sent e1 && e1 targets p ==> e1.ballot == p.ballot && e1.value == p.value;
invariant p2b_updates_prev:      forall (e: eP2B, a: Acceptor, p: Proposer) :: sent e && e.ballot == a.prevBallot && p == proposerOf(e.ballot) ==> !(p is Prepare);
invariant p2b_ballot_values:     forall (e: eP2B, p: Proposer) :: sent e ==> e targets p == (e.ballot == p.ballot && e.value == p.value);
// invariant p2b_means_voted:       forall (e: eP2B, a: Acceptor) :: (sent e && e.acceptor == a) == (MkPair(e.ballot, e.value) in a.voted);

// eDecide
invariant decided_from_proposer: forall (e: eDecide) :: sent e ==> e.proposer in proposers();
invariant decision_valid: forall (e: eDecide, p: Proposer) :: sent e && e.proposer == p ==> e.ballot == p.ballot && e.value == p.value;
invariant decision_from_propose: forall (e1: eDecide, e2: eP2A) :: sent e1 && sent e2 && e1.proposer == e2.proposer ==> e1.ballot == e2.ballot && e1.value == e2.value;
invariant done_after_decision: forall (e: eDecide, p: Proposer) :: sent e && e.proposer == p ==> p is Done;

// Proposer states
invariant highest_ballot_valid: forall (p: Proposer) :: p.highestBallot >= nullBallot();
invariant vote_received_same:   forall (p: Proposer, a: machine) :: a in p.p2bReceived ==> p.p2bReceived[a].ballot == p.ballot && p.p2bReceived[a].value == p.value;

// Acceptor states
invariant prev_ballot_valid_ge_null: forall (a: Acceptor) :: a.prevBallot >= nullBallot();
invariant promised_ge_accepted: forall (a: Acceptor) :: a.promised >= a.prevBallot;
invariant value_ballot_pair: forall (a: Acceptor) :: (a.prevBallot == nullBallot()) == (a.prevValue == nullValue());
invariant prev_ballot_valid: forall (a: Acceptor) :: (a.prevBallot != nullBallot()) ==> proposerOf(a.prevBallot) in proposers();
// invariant proposer_state_implied:  forall (a: Acceptor, p: Proposer) :: a.prevBallot != nullBallot() && p == proposerOf(a.prevBallot) ==> (p is Proposing || p is Done);
// invariant prev_value_valid: forall (a: Acceptor, p: Proposer) :: a.prevBallot != nullBallot() && p == proposerOf(a.prevBallot) ==> p.value == a.prevValue;
// cannot verify
// invariant prev_value_valid: forall (a: Acceptor, p: Proposer) :: a.prevBallot != nullBallot() && p == proposerOf(a.prevBallot) ==> (p is Proposing || p is Done);
