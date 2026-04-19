import assert from 'assert';
import { AnimationSequencer, animationSequencerCreate } from 'glov/client/animation';
import { MODE_DEVELOPMENT } from 'glov/client/client_config';
import { setState } from 'glov/client/engine';
import { ALIGN, fontStyle } from 'glov/client/font';
import { eatAllInput, mouseDownAnywhere } from 'glov/client/input';
import { ClientChannelWorker, netSubs, netUserId } from 'glov/client/net';
import { ScrollArea, scrollAreaCreate } from 'glov/client/scroll_area';
import {
  button,
  buttonText,
  drawRect,
  modalDialog,
  modalTextEntry,
  uiButtonWidth,
  uiGetFont,
  uiTextHeight,
} from 'glov/client/ui';
import * as urlhash from 'glov/client/urlhash';
import { DISPLAY_NAME_MAX_VISUAL_SIZE } from 'glov/common/net_common';
import type { RoomListResponse, RoomRecord, RoomRequest, RoomResponse } from '../server/roomlist_worker';
import { createAccountUI } from './account_ui';
import {
  BUTTON_HEIGHT,
  FONT_HEIGHT,
  game_height,
  game_width,
  GameStateSerialized,
  getLevelDefs,
  playInit,
  playNewGameState,
} from './main';
import { PAL_BLACK, PAL_BORDER, PAL_WHITE, palette, palette_font } from './palette';

urlhash.register({
  key: 'room',
  change: function (new_value: string): void {
    // TODO
  },
});

let account_ui: ReturnType<typeof createAccountUI>;

let net_msg: string | null = null;

let title_anim: AnimationSequencer | null = null;
let title_alpha = {
  title: 0,
  sub: 0,
  button: 0,
};
function stateTitleInitOnce(): void {
  account_ui = createAccountUI();
  // eslint-disable-next-line @typescript-eslint/no-use-before-define
  netSubs().onLogin(onLogin);

  title_anim = animationSequencerCreate();
  let t = 0;

  t = title_anim.add(0, 300, (progress) => {
    title_alpha.title = progress;
  });
  t = title_anim.add(t + 300, 300, (progress) => {
    title_alpha.sub = progress;
  });
  title_anim.add(t + 500, 300, (progress) => {
    title_alpha.button = progress;
  });
}
const style_title = fontStyle(null, {
  color: palette_font[PAL_WHITE],
  outline_color: palette_font[8],
  outline_width: 4,
});

function preLogout(): void {
  // if (test_room) {
  //   assert(test_room.numSubscriptions());
  //   test_room.unsubscribe();
  //   chat_ui.setChannel(null);
  //   test_room = null;
  //   if (!ROOM_REQUIRES_LOGIN) {
  //     setTimeout(getRoom, 1);
  //   }
  // }
}

let roomlist_loaded = false;
let room_list: RoomRecord[] = [];
function updateRooms(): void {
  netSubs().getChannel('roomlist.the', false).send<RoomListResponse>('list_get', null, function (err, resp) {
    if (err || !resp) {
      // ignore for now
      return;
    }
    roomlist_loaded = true;
    room_list = resp.rooms;
    // TODO: periodically re-check
  });
}

function onLogin(): void {
  updateRooms();
}

function onBadJoin(): void {
  net_msg = 'Error: room not initialized, try refreshing or navigating back to the title screen';
}

function joinRoom(ask_permission: boolean, room_id: string, on_init: (channel: ClientChannelWorker) => void): void {
  net_msg = 'Joining...';

  function doit(): void {
    let channel = netSubs().getChannel(`multiplayer.${room_id}`, true);
    channel.onceSubscribe(function () {
      let game_state = channel.getChannelData<GameStateSerialized>('public.gs', null!);
      if (!game_state) {
        on_init(channel);
      } else {
        assert.equal(typeof game_state.ld_idx, 'number');
        let player_idx = -1;
        let open_slot = false;
        for (let ii = 0; ii < game_state.players.length; ++ii) {
          if (game_state.players[ii].user_id === netUserId()) {
            player_idx = ii;
          } else if (!game_state.players[ii].user_id) {
            open_slot = true;
          }
        }
        if (player_idx !== -1) {
          net_msg = null;
          playInit(game_state.ld_idx, player_idx, channel);
          return;
        }
        channel.unsubscribe();
        // not auth'd to room
        if (!open_slot || ask_permission) {
          // TODO: spectate?
          return onBadJoin();
        }
        // Try again with permission
        ask_permission = true;
        // eslint-disable-next-line @typescript-eslint/no-use-before-define
        askPermission();
      }
    });
  }

  function askPermission(): void {
    netSubs().getChannel('roomlist.the', false).send<RoomResponse, string>('room_join', room_id,
      function (err, resp) {
        if (err || !resp) {
          net_msg = err || 'empty response';
          throw err;
        }
        urlhash.set('room', resp.room_id);
        doit();
      }
    );
  }

  if (ask_permission) {
    askPermission();
  } else {
    doit();
  }
}


function newGame(idx: number): void {
  net_msg = 'Allocating room...';
  netSubs().getChannel('roomlist.the', false).send<RoomResponse, RoomRequest>('room_alloc', {
    level_idx: idx,
    num_players: getLevelDefs()[idx].players,
  }, function (err, resp) {
    if (err || !resp) {
      net_msg = err || 'empty response';
      throw err;
    }
    urlhash.set('room', resp.room_id);
    joinRoom(false, resp.room_id, function (channel) {
      net_msg = 'Initializing new game...';
      if (resp.player_idx !== 0) {
        net_msg = 'Error: game not yet initialized, try reloading';
        return;
      }
      let ser = playNewGameState(idx);
      ser.players[resp.player_idx].user_id = netUserId()!;
      channel.send('init', ser, function () {
        net_msg = null;
        playInit(idx, resp.player_idx, channel);
      });
    });
  });
}

let room_scroll_area: ScrollArea;

export function getDisplayName(user_id: string): string {
  let is_left = user_id.startsWith('left:');
  if (is_left) {
    user_id = user_id.slice(5);
  }
  let ret = netSubs().getChannelImmediate(`user.${user_id}`).getChannelData('public.display_name', '???');
  if (is_left) {
    ret += ' (left)';
  } else if (user_id === netUserId()) {
    ret += ' (ME)';
  }
  return ret;
}

let done_once = false;
function stateTitle(dt: number): void {
  if (!done_once) {
    done_once = true;
    stateTitleInitOnce();
  }

  let font = uiGetFont();
  let text_height = uiTextHeight();

  let W = game_width;
  let H = game_height;

  if (title_anim && (mouseDownAnywhere() || MODE_DEVELOPMENT)) {
    title_anim.update(Infinity);
    title_anim = null;
  }
  if (title_anim) {
    if (!title_anim.update(dt)) {
      title_anim = null;
    } else {
      eatAllInput();
    }
  }

  let y = 30;

  font.draw({
    style: style_title,
    alpha: title_alpha.title,
    x: 0, y, w: W, align: ALIGN.HCENTER,
    size: text_height * 3,
    text: 'Drone Supervisor II',
  });
  y += text_height * 3 + 8;

  if (!netSubs().loggedIn()) {

    account_ui.showLogin({
      x: game_width / 2, y,
      text_w: game_width / 2,
      prelogout: preLogout, center: true,
      style: fontStyle(null, {
        outline_width: 2,
        outline_color: 0xFFFFFFff,
        color: 0x000000ff,
      }),
    });

    return;
  }

  let button_width = uiButtonWidth();
  if (button({
    x: game_width - button_width - 4,
    y: 4,
    text: 'Log out',
  })) {
    netSubs().logout();
  }
  let disp_name = netSubs().getDisplayName() || netSubs().getUserId()!;
  font.draw({
    color: palette_font[PAL_WHITE],
    x: button_width + 8, y: 4, align: ALIGN.VCENTER | ALIGN.HCENTERFIT,
    w: game_width - (button_width + 8) * 2,
    h: BUTTON_HEIGHT,
    text: `Welcome, ${disp_name}!`
  });
  if (button({
    x: 4,
    y: 4,
    text: 'Change Name',
  })) {
    modalTextEntry({
      title: 'Change Display Name',
      edit_text: disp_name,
      max_visual_size: DISPLAY_NAME_MAX_VISUAL_SIZE,
      buttons: {
        OK: function (new_name) {
          if (new_name) {
            netSubs().getMyUserChannel()!.cmdParse(`rename ${new_name}`, (err) => {
              if (err) {
                console.log(err);
              }
            });
          }
        },
        Cancel: null,
      }
    });
  }

  font.draw({
    color: palette_font[PAL_WHITE],
    alpha: title_alpha.sub,
    x: 0,
    y: H - text_height - 2,
    w: W, align: ALIGN.HCENTER,
    text: 'Made in 48 hours by Jimb Esser for Ludum Dare 59 and Gamedev.js Jam 2026',
  });

  if (urlhash.get('room') && !net_msg) {
    joinRoom(true, urlhash.get('room'), onBadJoin);
  }

  if (net_msg) {
    y += 20;
    font.draw({
      x: 0, y, w: W,
      align: ALIGN.HCENTER,
      text: net_msg,
    });

    return;
  }

  if (!title_alpha.button) {
    return;
  }
  let color = [1,1,1, title_alpha.button] as const;

  let level_defs = getLevelDefs();

  let button_w = BUTTON_HEIGHT * 3;
  let button_h = BUTTON_HEIGHT;
  let button_param = {
    color,
    w: button_w,
    h: button_h,
  };
  for (let ii = 0; ii < level_defs.length; ++ii) {
    let ld = level_defs[ii];
    if (ld.name === 'debug') {
      continue;
    }

    let best_room: RoomRecord | undefined;
    for (let jj = 0; jj < room_list.length; ++jj) {
      let entry = room_list[jj];
      if (entry.level_idx === ii) {
        best_room = entry;
      }
    }
    let can_resume = best_room && best_room.players.includes(netUserId()!);

    let x = (game_width - button_param.w * 3 - 4 * 3 - 60) / 2;
    font.draw({
      x, y,
      alpha: title_alpha.button,
      h: BUTTON_HEIGHT,
      align: ALIGN.VCENTER,
      text: ld.name,
    });
    x += 60;
    if (button({
      ...button_param,
      x, y,
      text: 'New Game',
    })) {
      if (best_room) {
        let game_idx = ii;
        modalDialog({
          title: 'Start New Game?',
          text: can_resume ?
              'You already have a game in progress, are you sure you wish to start a new one?' +
                '\n\nNote: your previous 10 games will still be saved if you ever want to return to them.' :
              'There are games with open slots available for you to join, are you sure you want to start a new one?',
          buttons: {
            yes: function () {
              newGame(game_idx);
            },
            no: null,
          },
        });
      } else {
        newGame(ii);
      }
    }
    x += button_w + 4;

    if (button({
      ...button_param,
      x, y,
      disabled: !best_room,
      text: can_resume ? 'Resume' : 'Join',
    })) {
      urlhash.set('room', best_room!.room_id);
      joinRoom(!can_resume, best_room!.room_id, onBadJoin);
    }
    x += button_w + 4;

    if (ii !== 0 && button({
      ...button_param,
      x, y,
      text: 'Scores',
    })) {
      // TODO
    }
    x += button_w + 4;

    y += BUTTON_HEIGHT + 4;
  }

  if (!roomlist_loaded) {
    font.draw({
      x: 0, y, w: W,
      align: ALIGN.HCENTER,
      text: 'Loading room list...',
    });
    return;
  }


  if (!room_scroll_area) {
    room_scroll_area = scrollAreaCreate({
      background_color: null,
      auto_hide: true,
    });
  }
  room_scroll_area.begin({
    x: 0, w: W,
    y, h: game_height - y - text_height - 4,
  });
  y = 1;
  let x = 16;
  W -= 32;

  font.draw({
    x, y, w: W,
    text: 'Previous Games / Open Rooms',
    align: ALIGN.HCENTER,
  });
  y += FONT_HEIGHT + 2;

  button_w = (W - 4) / 2;
  button_h = text_height * 4;
  let join_button_w = BUTTON_HEIGHT * 3;
  let join_button_h = (button_h - 2) / 2;

  let x0 = x;
  let z = Z.UI;

  for (let ii = 0; ii < room_list.length; ++ii) {
    let entry = room_list[ii];
    let ld = level_defs[entry.level_idx];
    let y_save = y;
    let has_me = entry.players.includes(netUserId()!);
    drawRect(x-1, y-1, x + button_w+1, y + button_h+1, z - 0.1,
      has_me ? palette[15] : palette[PAL_BLACK]);

    if (buttonText({
      x: x + button_w - join_button_w,
      y,
      z,
      w: join_button_w,
      h: join_button_h,
      text: has_me ? 'Resume' : 'Join',
    })) {
      urlhash.set('room', entry.room_id);
      joinRoom(!has_me, entry.room_id, onBadJoin);
    }
    if (has_me) {
      if (buttonText({
        x: x + button_w - join_button_w,
        y: y + join_button_h + 2,
        z,
        w: join_button_w,
        h: join_button_h,
        text: entry.players.length > 1 ? 'Leave' : 'Delete',
      })) {
        room_list.splice(ii, 1);
        netSubs().getChannel('roomlist.the', false).send<RoomResponse, string>('forget', entry.room_id, function () {
          // ignore response
        });
      }
    }

    font.draw({
      x, y, z,
      text: `${ld.name} ${entry.players.length}/${entry.num_players}P (${entry.room_id})`,
    });
    y += text_height;
    let players = entry.players;
    if (0) {
      players = players.concat(players);
      players = players.concat(players);
    }
    font.draw({
      x, y, z,
      w: button_w - join_button_w - 1,
      align: ALIGN.HWRAP,
      text: players.map(getDisplayName).join(', '),
    });
    y += text_height * 3 + 4;
    // hide overflow
    drawRect(x, y - 3, x + button_w, y + 4 + text_height * 3, z + 0.1, palette[PAL_BORDER]);
    z++;

    if (!(ii % 2)) {
      y = y_save;
      x += button_w + 4;
    } else {
      x = x0;
    }
  }

  room_scroll_area.end(y);
}

export function titleReturn(): void {
  urlhash.set('room', '');
  roomlist_loaded = false;
  updateRooms();
  setState(stateTitle);
}

export function titleInit(): void {
  setState(stateTitle);
}
