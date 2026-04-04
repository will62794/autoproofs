# autoproofs
Experiments in autonomous protocol proofs.

Basically, we have an [inductive invariant](https://github.com/will62794/autoproofs/blob/b61461f42b530232af2f039851a80f1120dc8046/AbstractRaft_IndProofs_test.tla#L10-L23) developed for an abstract Raft protocol specification in TLA+. We want to see if Claude Opus 4.6 can go ahead and write a full TLAPS proof for this, with just some [basic instructions](AGENTS.md) and a [proof skeleton](https://github.com/will62794/autoproofs/blob/main/AbstractRaft_IndProofs_test.tla). 

See the [`proof-dev`](https://github.com/will62794/autoproofs/tree/proof-dev) branch for its results.
