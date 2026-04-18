LD59 - Theme Signal & Machines
============================

Ludum Dare 59 Entry by Jimbly - "Title TBD"

* Play here: [dashingstrike.com/LudumDare/LD59/](http://www.dashingstrike.com/LudumDare/LD59/)
* Using [Javascript libGlov/GLOV.js framework](https://github.com/Jimbly/glovjs)

Acknowledgements:
* TODO

Start with: `npm start` (after running `npm i` once)


TODO
====
Add simulation speed toggle divorced from walltime and rewards
* only give rewards when simulation day finishes *and* walltime requirement has passed

Questions:
* Can we upgrade day length?  If not, then we need faster locomotion / cannons, or longer days and a way to skip
* Either is probably fine for MP, other people's drones just run out of power sooner

Main screen:
* login / play as guest
* new game -> choose type -> warn if available to join already
* list all in-progress games we're in; list finished games of ours (at top, if we we haven't opened them yet); list games with open slots

Tutorial game (single-player, but still on server)
Multiplayer logic
  goal: total revenue / day

Additional recipes and resources (unique colored gems)

Show recipes somewhere (just open a recipe book overlay?  tooltip on each resource?)

Maybe
=====
* pause mode (continuous money in BG, just don't animate)
* button and hotkey to reset the day immediately (try doing this upon every placement near an actor?)
* undo/redo

Plan - Drone Supervisor II Online!
==================================

Primitives:
* drone
* rotate clockwise/counter-clockwise
* 2-input crafting machine - must be delivered simultaneously or output is input
* stop (free)
* go - radius 5-7ish? (free)
* 1-input storage
* (multiplayer) sign

Upgrades:
* Drone battery

Resources:
* fruit (apples)
* wood
* stone
* 3 colored gems (1 per player)


Goal ~8 specific recipes?
fruit + ? = fruit
fruit + wood = beer
fruit + stone = jam (or fruit + fruit?)
wood + stone = fire
wood + ? = wood
stone + ? = stone

beer + fire = game
beer + stone = acid
jam + fruit = pie
game + jam = LD
