#Coerceo in Idris

Coerceo is an original board game that served as a basis for the first
*codelympics* project.

This is my unfinished submission. The goal was to create a "game reader".
Games are recorded with a set of characters, akin to what's used in chess.
The intent is to (someday being able to) read such a recording to check its
validity.

Idris is a general purpose dependently typed pure functional programming
language. This is a lot of words to just say that Idris is awesome, as the
compiler is able to prove that the program is correct and will terminate.

## What is Coerceo

Coerceo is an awesome board game akin to GO and checkers.

You play with tetrahedral pieces on a shriking hex board ; the goal: being the
last one on it.

Checkout [the website](http://coerceo.com). (btw, the publisher of the game
is an awesome guy)

## Why Idris?

If you can deserialize a game record, then it must be valid (according
to how you defined validity in the first place, which could be wrong).
Indeed, because of Idris, we know that a game in memory should be well
defined as long as it is of the right type.

The program is therefore same. Plus, Idris is also a theorem prover,
so we can verify the assumptions we make. 

It greatly reduces the spectrum of possible mistakes, leaving the
potentiel liabilities in a realm much less obscure than the internals of a
program.

I haven't sorted this all out yet ; the benefits of the language might
be discovered as I work on the project.

## The codelympics

Visit [the website](http://codelympics.io) to know more about the initiative
of the project.

The fundamental idea is simple: to finish (or at least engage significantly in)
a side project, it's much better to have deadlines, competition, and people to
talk about it.

## What is to be expected

The following core features are essential and should be implemented in the following
weeks:

- Representing the board in memory (done)
- Initializing the board (done)
- Moving the pieces
- Capturing the pieces
- Shriking the board
- Sniping the pieces
- Managing game state
- Deserializing a game
- Serializing a game

Then, we could do the following improvements:

- Connect this to a UI, in order to actually visualize/play the game
- Connect this to a database for competitive plays, strategy analysis, AI or
whatnot
- Create a DSL to interact with the game ; this can open up to a lot of other
applications (I might actually do that for deserializing)

## Licensing

I'm not good at this, so, whatever is needed to state that anything related
to Coerceo (concept, artwork, trademark, etc.) belongs to the publishing
company of the Coerceo.

I don't know what's the implication on my code though. But I don't care.
