# apollo11-verified

Formalizing Apollo 11 guidance software.

This repository begins a full formalization of the Apollo 11 Apollo Guidance
Computer mission software as transcribed in
[`chrislgarry/Apollo-11`](https://github.com/chrislgarry/Apollo-11). The
initial scope covers both mission builds in that referent repository:

- `Luminary099` for the Lunar Module
- `Comanche055` for the Command Module

The first formalization pass is intentionally architectural. It sets up a
shared semantic vocabulary for:

- the paired mission programs and their vehicle assignments
- common AGC executive behavior such as jobs, alarms, restarts, and display flow
- LM-specific powered descent and ascent phases
- CM-specific entry and reentry phases
- subsystem ownership derived from the source tree layout

The scaffold is grounded in the structure of the referent source tree,
especially these files:

- `Luminary099/EXECUTIVE.agc`
- `Luminary099/ALARM_AND_ABORT.agc`
- `Luminary099/THE_LUNAR_LANDING.agc`
- `Luminary099/LUNAR_LANDING_GUIDANCE_EQUATIONS.agc`
- `Luminary099/THROTTLE_CONTROL_ROUTINES.agc`
- `Luminary099/ASCENT_GUIDANCE.agc`
- `Comanche055/EXECUTIVE.agc`
- `Comanche055/CM_ENTRY_DIGITAL_AUTOPILOT.agc`
- `Comanche055/REENTRY_CONTROL.agc`

## Initial contents

- `bookplate.v`: approved bookplate
- `Apollo11.v`: commented semantic scaffold and first structural lemmas

## Near-term proof plan

1. Define a small-step semantics for the shared AGC executive core.
2. Refine alarm and restart behavior against the Apollo 11 source comments.
3. Model the LM descent stack around `P63`, `P64`, `P65`, and `P66/P67`.
4. Model the CM entry and digital autopilot path.
5. State and prove mission-phase safety invariants that connect scheduler state,
   alarms, and allowed subsystem transitions.
