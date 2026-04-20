LD59 - Themes "Signal" & "Machines"
============================

Ludum Dare 59 and Gamedev.js '26 Entry by Jimbly - "Drone Supervisor II Online"

Async multiplayer online automation game

* Play here: [dashingstrike.com/dronesup2/](http://www.dashingstrike.com/dronesup2/)
* Also available on [Wavedash](https://wavedash.com/games/drone-supervisor-2) and [Itch.io](https://dashingstrike.itch.io/drone-supervisor-2)
* Using [JavaScript GLOV.js framework](https://github.com/Jimbly/glovjs)

Acknowledgements:
* Palette - https://lospec.com/palette-list/arq16
* Predecessor - https://ldjam.com/events/ludum-dare/39/drone-supervisor
* Inspiration: _Leap Day_ by _Spryfox_

Running
* Only pre-requisite: Node.js v22 (some dependencies may or may not work on newer versions of Node.js depending on your OS - if in doubt, install Node.js v22 with NVS or NVM)
* Start with: `npm start` (after running `npm i` once)

TODO
====

* Show finished state of games on room list - encourage user to resume a game that has been won but they haven't seen the victory for it yet (and save a high score when they do)
  *  Also some progress - encourage joining games with players actively playing

Maybe TODO
==========
* rate-limit sending diffs
* pause mode (continuous money in BG, just don't animate)
* button and hotkey to reset the day immediately (try doing this upon every placement near an actor?)
* undo/redo
* get default name for new anonymous account for scores local storage
