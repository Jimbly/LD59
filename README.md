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

Additional recipes and resources

offline time pay out logarithmically
floaters look bad when two drones sell 2 things on the same frame, add an offset
Show finished state of games on room list - encourage user to resume a game that has been won but they haven't seen the victory for it yet (and save a high score when they do)
  Also some progress - encourage joining games with players actively playing
get default name for new anonymous account for scores local storage

Maybe
=====
* rate-limit sending diffs
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
