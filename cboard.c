/* vim:tw=78:ts=8:sw=4:set ft=c:  */
/*
    Copyright (C) 2002-2015 Ben Kibbey <bjk@luxsci.net>

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <string.h>
#include <errno.h>
#include <ctype.h>
#include <pwd.h>
#include <signal.h>
#include <time.h>
#include <err.h>
#include <locale.h>

#ifdef HAVE_STDARG_H
#include <stdarg.h>
#endif

#ifdef HAVE_SYS_WAIT_H
#include <sys/wait.h>
#endif

#ifdef HAVE_REGEX_H
#include <regex.h>
#endif

#ifdef WITH_LIBPERL
#include "perl-plugin.h"
#endif

#include "common.h"
#include "conf.h"
#include "window.h"
#include "message.h"
#include "colors.h"
#include "input.h"
#include "misc.h"
#include "engine.h"
#include "strings.h"
#include "menu.h"
#include "keys.h"
#include "rcfile.h"
#include "filebrowser.h"

#ifdef DEBUG
#include <debug.h>
#endif

#define COPYRIGHT	        "Copyright (C) 2002-2015 " PACKAGE_BUGREPORT
#define LINE_GRAPHIC(c) 	((!config.linegraphics) ? ' ' : c)
#define ROWTOMATRIX(r)  	((8 - r) * 2 + 2 - 1)
#define COLTOMATRIX(c)  	((c == 1) ? 1 : c * 4 - 3)
#define STATUS_HEIGHT		12
#define MEGA_BOARD		(LINES >= 50 && COLS >= 144)
#define BOARD_HEIGHT_MB		50
#define BOARD_WIDTH_MB		98
#define STATUS_WIDTH_MB		(COLS - BOARD_WIDTH_MB)
#define TAG_HEIGHT_MB		31
#define TAG_WIDTH_MB		(COLS - BOARD_WIDTH_MB)
#define HISTORY_HEIGHT_MB	(LINES - (STATUS_HEIGHT + TAG_HEIGHT_MB + 1))
#define HISTORY_WIDTH_MB	(COLS - BOARD_WIDTH_MB)
#define BIG_BOARD		(LINES >= 40 && COLS >= 112)
#define BOARD_HEIGHT		((MEGA_BOARD) ? BOARD_HEIGHT_MB : (BIG_BOARD) ? 34 : 18)
#define BOARD_WIDTH		((MEGA_BOARD) ? BOARD_WIDTH_MB : (BIG_BOARD) ? 66 : 34)
#define STATUS_WIDTH		((MEGA_BOARD) ? STATUS_WIDTH_MB : COLS - BOARD_WIDTH)
#define TAG_HEIGHT		((MEGA_BOARD) ? TAG_HEIGHT_MB : LINES - STATUS_HEIGHT - 1)
#define TAG_WIDTH		((MEGA_BOARD) ? TAG_WIDTH_MB : COLS - BOARD_WIDTH)
#define HISTORY_HEIGHT		((MEGA_BOARD) ? HISTORY_HEIGHT_MB : LINES - BOARD_HEIGHT)
#define HISTORY_WIDTH		((MEGA_BOARD) ? HISTORY_WIDTH_MB : COLS - STATUS_WIDTH)
#define MAX_VALUE_WIDTH	        (COLS - 8)

enum {
    UP, DOWN, LEFT, RIGHT
};

static WINDOW *boardw;
static PANEL *boardp;
static WINDOW *tagw;
static PANEL *tagp;
static WINDOW *statusw;
static PANEL *statusp;
static WINDOW *historyw;
static PANEL *historyp;
static WINDOW *loadingw;
static PANEL *loadingp;
static WINDOW *enginew;
static PANEL *enginep;

static char gameexp[255];
static char moveexp[255];
static struct itimerval clock_timer;
static int delete_count = 0;
static int markstart = -1, markend = -1;
static int keycount;
static char loadfile[FILENAME_MAX];
static int quit;
static wint_t input_c;

// Loaded filename from the command line or from the file input dialog.
static int filetype;
enum {
    FILE_NONE, FILE_PGN, FILE_FEN, FILE_EPD
};

static char **nags;
static int nag_total;
static int macro_match;

// Primer movimiento de juego cargado
// First move loaded game
static char fm_loaded_file = FALSE;

static int COLS_OLD, LINES_OLD;

// Status window.
static struct {
  wchar_t *notify;	// The status window notification line buffer.
} status;

static int curses_initialized;

// When in history mode a full step is to the next move of the same playing
// side. Half stepping is alternating sides.
static int movestep;

static wchar_t *w_pawn_wchar;
static wchar_t *w_rook_wchar;
static wchar_t *w_bishop_wchar;
static wchar_t *w_knight_wchar;
static wchar_t *w_queen_wchar;
static wchar_t *w_king_wchar;
static wchar_t *b_pawn_wchar;
static wchar_t *b_rook_wchar;
static wchar_t *b_bishop_wchar;
static wchar_t *b_knight_wchar;
static wchar_t *b_queen_wchar;
static wchar_t *b_king_wchar;
static wchar_t *empty_wchar;
static wchar_t *enpassant_wchar;

static wchar_t *yes_wchar;
static wchar_t *all_wchar;         // do_save_game_overwrite_confirm()
static wchar_t *overwrite_wchar;   // do_save_game_overwrite_confirm()
static wchar_t *resume_wchar;      // do_history_mode_confirm()
static wchar_t *current_wchar;     // do_game_save_multi_confirm()
static wchar_t *append_wchar;      // save_pgn()

static const char piece_chars[] = "PpRrNnBbQqKkxx";
static char *translatable_tag_names[7];
static const char *f_pieces[] = {
    "       ",	// 0
    "   O   ",
    "  /_\\  ",
    " |-|-| ",	// 3
    "  ] [  ",
    " /___\\ ",
    "  /?M  ",	// 6
    " (@/)) ",
    "  /__))",
    "   O   ",	// 9
    "  (+)  ",
    "  /_\\  ",
    "•°°°°°•",// 12
    " \\\\|// ",
    " |___| ",
    " __+__ ",	// 15
    "(__|__)",
    " |___| ",
    "  \\ /  ",	// 18
    "   X   ",
    "  / \\  "
};

static const bool cb[8][8] = {
    {1,0,1,0,1,0,1,0},
    {0,1,0,1,0,1,0,1},
    {1,0,1,0,1,0,1,0},
    {0,1,0,1,0,1,0,1},
    {1,0,1,0,1,0,1,0},
    {0,1,0,1,0,1,0,1},
    {1,0,1,0,1,0,1,0},
    {0,1,0,1,0,1,0,1}
};

static void free_userdata_once(GAME g);
static void do_more_help(WIN *);

void coordofmove(GAME g, char *move, char *prow, char *pcol)
{
    char l = strlen(move);

    if (*move == 'O') {
        *prow = (g->turn == WHITE) ? 8 : 1;
        *pcol = (l <= 4) ? 7 : 3;
        return;
    }

    move += l;

    while (!isdigit(*move))
	move--;

    *prow = RANKTOINT(*move--);
    *pcol = FILETOINT(*move);
}

#define INV_INT(x) (9 - x)
#define INV_INT0(x) (7 - x)

// Posición por rotación de tablero.
// Rotation board position.
void rotate_position(char *prow, char *pcol)
{
  *prow = INV_INT(*prow);
  *pcol = INV_INT(*pcol);
}

void update_cursor(GAME g, int idx)
{
    int t = pgn_history_total(g->hp);
    struct userdata_s *d = g->data;

    /*
     * If not deincremented then r and c would be the next move.
     */
    idx--;

    if (idx > t || idx < 0 || !t || !g->hp[idx]->move)
	d->c_row = 2, d->c_col = 5;
    else
        coordofmove(g, g->hp[idx]->move, &d->c_row, &d->c_col);

    if (d->mode == MODE_HISTORY && d->rotate)
	rotate_position(&d->c_row, &d->c_col);
}

static int init_nag()
{
    FILE *fp;
    char line[LINE_MAX];
    int i = 0;

    if ((fp = fopen(config.nagfile, "r")) == NULL) {
	cmessage(ERROR_STR, ANY_KEY_STR, "%s: %s", config.nagfile, strerror(errno));
	return 1;
    }

    nags = Realloc(nags, (i+2) * sizeof(char *));
    nags[i++] = strdup(_("none"));
    nags[i] = NULL;

    while (!feof(fp)) {
	if (fscanf(fp, " %[^\n] ", line) == 1) {
	    nags = Realloc(nags, (i + 2) * sizeof(char *));
	    nags[i++] = strdup(line);
	}
    }

    nags[i] = NULL;
    nag_total = i;
    fclose(fp);
    return 0;
}

void edit_nag_toggle_item(struct menu_input_s *m)
{
    struct input_s *in = m->data;
    struct input_data_s *id = in->data;
    HISTORY *h = id->data;
    int i;

    if (m->selected == 0) {
	for (i = 0; i < MAX_PGN_NAG; i++)
	    h->nag[i] = 0;

	for (i = 0; m->items[i]; i++)
	    m->items[i]->selected = 0;

	return;
    }

    for (i = 0; i < MAX_PGN_NAG; i++) {
	if (h->nag[i] == m->selected)
	    h->nag[i] = m->selected = 0;
	else {
	    if (!h->nag[i]) {
		h->nag[i] = m->selected;
		break;
	    }
	}
    }
}

void edit_nag_save(struct menu_input_s *m)
{
    pushkey = -1;
}

void edit_nag_help(struct menu_input_s *m)
{
    message(_("NAG Menu Keys"), ANY_KEY_STR, "%s",
	    _ (
	       "    UP/DOWN - previous/next menu item\n"
	       "   HOME/END - first/last menu item\n"
	       "  PGDN/PGUP - next/previous page\n"
	       "  a-zA-Z0-9 - jump to item\n"
	       "      SPACE - toggle selected item\n"
	       "     CTRL-X - quit with changes"
	       ));
}

struct menu_item_s **get_nag_items(WIN *win)
{
    int i, n;
    struct menu_input_s *m = win->data;
    struct input_s *in = m->data;
    struct input_data_s *id = in->data;
    struct menu_item_s **items = m->items;
    HISTORY *h = id->data;

    if (items) {
	for (i = 0; items[i]; i++)
	    free(items[i]);
    }

    for (i = 0; nags[i]; i++) {
	items = Realloc(items, (i+2) * sizeof(struct menu_item_s *));
	items[i] = Malloc(sizeof(struct menu_item_s));
	items[i]->name = nags[i];
	items[i]->value = NULL;

	for (n = 0; n < MAX_PGN_NAG; n++) {
	    if (h->nag[n] == i) {
		items[i]->selected = 1;
		n = -1;
		break;
	    }
	}

	if (n >= 0)
	    items[i]->selected = 0;
    }

    items[i] = NULL;
    m->nofree = 1;
    m->items = items;
    return items;
}

void nag_print(WIN *win)
{
    struct menu_input_s *m = win->data;

    mvwprintw(win->w, m->print_line, 1, "%-*s", win->cols - 2, m->item->name);
}

void edit_nag(void *arg)
{
    struct menu_key_s **keys = NULL;

    if (!nags) {
	if (init_nag())
	    return;
    }

    add_menu_key(&keys, ' ', edit_nag_toggle_item);
    add_menu_key(&keys, CTRL_KEY('x'), edit_nag_save);
    add_menu_key(&keys, KEY_F(1), edit_nag_help);
    construct_menu(0, 0, -1, -1, _("Numeric Annotation Glyphs"), 1, get_nag_items, keys, arg,
	    nag_print, NULL);
    return;
}

static void *view_nag(void *arg)
{
    HISTORY *h = (HISTORY *)arg;
    char buf[80];
    char line[LINE_MAX] = {0};
    int i = 0;

    snprintf(buf, sizeof(buf), "%s \"%s\"", _("Viewing NAG for"), h->move);

    if (!nags) {
	if (init_nag())
	    return NULL;
    }

    for (i = 0; i < MAX_PGN_NAG; i++) {
        char buf2[16];

	if (!h->nag[i])
	    break;

	if (h->nag[i] >= nag_total)
	  strncat(line, itoa(h->nag[i], buf2), sizeof(line)-1);
	else
	    strncat(line, nags[h->nag[i]], sizeof(line)-1);

	strncat(line, "\n", sizeof(line)-1);
    }

    line[strlen(line) - 1] = 0;
    message(buf, ANY_KEY_STR, "%s", line);
    return NULL;
}

void view_annotation(HISTORY *h)
{
    char buf[MAX_SAN_MOVE_LEN + strlen(_("Viewing Annotation for")) + 4];
    int nag = 0, comment = 0;

    if (!h)
	return;

    if (h->comment && h->comment[0])
        comment++;

    if (h->nag[0])
 	nag++;

    if (!nag && !comment)
	return;

    snprintf(buf, sizeof(buf), "%s \"%s\"", _("Viewing Annotation for"), h->move);

    if (comment)
	construct_message(buf, (nag) ? _("Any other key to continue") : ANY_KEY_STR, 0, 1,
		(nag) ? _("Press 'n' to view NAG") : NULL,
		(nag) ? view_nag : NULL, (nag) ? h : NULL, NULL,
		(nag) ? 'n' : 0, 0, "%s", h->comment);
    else
	construct_message(buf, _("Any other key to continue"), 0, 1, _("Press 'n' to view NAG"), view_nag, h, NULL,
		'n', 0, "%s", _("No comment text for this move"));
}

int do_game_write(char *filename, char *mode, int start, int end)
{
    int i;
    struct userdata_s *d;
    PGN_FILE *pgn;

    i = pgn_open(filename, mode, &pgn);

    if (i == E_PGN_ERR) {
	cmessage(ERROR_STR, ANY_KEY_STR, "%s\n%s", filename, strerror(errno));
	return 1;
    }
    else if (i == E_PGN_INVALID) {
	cmessage(ERROR_STR, ANY_KEY_STR, "%s\n%s", filename, _("Not a regular file"));
	return 1;
    }

    for (i = (start == -1) ? 0 : start; i < end; i++) {
	d = game[i]->data;
	pgn_write(pgn, game[i]);
	CLEAR_FLAG(d->flags, CF_MODIFIED);
    }

    if (pgn_close(pgn) != E_PGN_OK)
	message(ERROR_STR, ANY_KEY_STR, "%s", strerror(errno));

    if (start == -1) {
	strncpy(loadfile, filename, sizeof(loadfile));
	loadfile[sizeof(loadfile)-1] = 0;
    }

    return 0;
}

struct save_game_s {
    char *filename;
    char *mode;
    int start;
    int end;
};

void do_save_game_overwrite_confirm(WIN *win)
{
    char *mode = "w";
    struct save_game_s *s = win->data;
    wchar_t str[] =  { win->c, 0 };

    if (!wcscmp (str, append_wchar))
        mode = "a";
    else if (!wcscmp (str, overwrite_wchar))
        mode = "w";
    else
        goto done;

    if (do_game_write(s->filename, mode, s->start, s->end))
	update_status_notify(gp, "%s", _("Save game failed."));
    else
	update_status_notify(gp, "%s", _("Game saved."));

done:
    free(s->filename);
    free(s);
}

/* If the saveindex argument is -1, all games will be saved. Otherwise it's a
 * game index number.
 */
void save_pgn(char *filename, int saveindex)
{
    char buf[FILENAME_MAX];
    struct stat st;
    int end = (saveindex == -1) ? gtotal : saveindex + 1;
    struct save_game_s *s;

    if (filename[0] != '/' && config.savedirectory) {
	if (stat(config.savedirectory, &st) == -1) {
	    if (errno == ENOENT) {
		if (mkdir(config.savedirectory, 0755) == -1) {
		    cmessage(ERROR_STR, ANY_KEY_STR, "%s: %s", config.savedirectory,
			    strerror(errno));
		    return;
		}
	    }
	    else {
		cmessage(ERROR_STR, ANY_KEY_STR, "%s: %s", config.savedirectory,
			strerror(errno));
		return;
	    }
	}

	if (stat(config.savedirectory, &st) == -1) {
            cmessage(ERROR_STR, ANY_KEY_STR, "%s: %s", config.savedirectory,
                     strerror(errno));
            return;
        }

	if (!S_ISDIR(st.st_mode)) {
	    cmessage(ERROR_STR, ANY_KEY_STR, "%s: %s", config.savedirectory, _("Not a directory."));
	    return;
	}

	snprintf(buf, sizeof(buf), "%s/%s", config.savedirectory, filename);
	filename = buf;
    }

    if (access(filename, W_OK) == 0) {
	s = Malloc(sizeof(struct save_game_s));
	s->filename = strdup(filename);
	s->start = saveindex;
	s->end = end;
	construct_message(NULL, _("What would you like to do?"), 0, 1, NULL,
			  NULL, s, do_save_game_overwrite_confirm, 0, 0,
			  "%s \"%s\"\nPress \"%ls\" to append to this file, \"%ls\" to overwrite or any other key to cancel.",
			  _("File exists:"), filename, append_wchar,
			  overwrite_wchar);
	return;
    }

    if (do_game_write(filename, "a", saveindex, end))
	update_status_notify(gp, "%s", _("Save game failed."));
    else
	update_status_notify(gp, "%s", _("Game saved."));
}

static int castling_state(GAME g, BOARD b, int row, int col, int piece, int mod)
{
    if (pgn_piece_to_int(piece) == ROOK && col == 7
	    && row == 7 &&
	    (TEST_FLAG(g->flags, GF_WK_CASTLE) || mod) &&
	    pgn_piece_to_int(b[7][4].icon) == KING && isupper(piece)) {
	if (mod)
	    TOGGLE_FLAG(g->flags, GF_WK_CASTLE);
	return 1;
    }
    else if (pgn_piece_to_int(piece) == ROOK && col == 0
	    && row == 7 &&
	    (TEST_FLAG(g->flags, GF_WQ_CASTLE) || mod) &&
	    pgn_piece_to_int(b[7][4].icon) == KING && isupper(piece)) {
	if (mod)
	    TOGGLE_FLAG(g->flags, GF_WQ_CASTLE);
	return 1;
    }
    else if (pgn_piece_to_int(piece) == ROOK && col == 7
	    && row == 0 &&
	    (TEST_FLAG(g->flags, GF_BK_CASTLE) || mod) &&
	    pgn_piece_to_int(b[0][4].icon) == KING && islower(piece)) {
	if (mod)
	    TOGGLE_FLAG(g->flags, GF_BK_CASTLE);
	return 1;
    }
    else if (pgn_piece_to_int(piece) == ROOK && col == 0
	    && row == 0 &&
	    (TEST_FLAG(g->flags, GF_BQ_CASTLE) || mod) &&
	    pgn_piece_to_int(b[0][4].icon) == KING && islower(piece)) {
	if (mod)
	    TOGGLE_FLAG(g->flags, GF_BQ_CASTLE);
	return 1;
    }
    else if (pgn_piece_to_int(piece) == KING && col == 4
	    && row == 7 &&
	    (mod || (pgn_piece_to_int(b[7][7].icon) == ROOK &&
	      TEST_FLAG(g->flags, GF_WK_CASTLE))
	      ||
	     (pgn_piece_to_int(b[7][0].icon) == ROOK &&
	      TEST_FLAG(g->flags, GF_WQ_CASTLE))) && isupper(piece)) {
	if (mod) {
	    if (TEST_FLAG(g->flags, GF_WK_CASTLE) ||
		    TEST_FLAG(g->flags, GF_WQ_CASTLE))
		CLEAR_FLAG(g->flags, GF_WK_CASTLE|GF_WQ_CASTLE);
	    else
		SET_FLAG(g->flags, GF_WK_CASTLE|GF_WQ_CASTLE);
	}
	return 1;
    }
    else if (pgn_piece_to_int(piece) == KING && col == 4
	    && row == 0 &&
	    (mod || (pgn_piece_to_int(b[0][7].icon) == ROOK &&
	      TEST_FLAG(g->flags, GF_BK_CASTLE))
	      ||
	     (pgn_piece_to_int(b[0][0].icon) == ROOK &&
	      TEST_FLAG(g->flags, GF_BQ_CASTLE))) && islower(piece)) {
	if (mod) {
	    if (TEST_FLAG(g->flags, GF_BK_CASTLE) ||
		    TEST_FLAG(g->flags, GF_BQ_CASTLE))
		CLEAR_FLAG(g->flags, GF_BK_CASTLE|GF_BQ_CASTLE);
	    else
		SET_FLAG(g->flags, GF_BK_CASTLE|GF_BQ_CASTLE);
	}
	return 1;
    }

    return 0;
}

#define IS_ENPASSANT(c)	(c == 'x') ? CP_BOARD_ENPASSANT : isupper(c) ? CP_BOARD_WHITE : CP_BOARD_BLACK
#define ATTRS(cp) (cp & (A_BOLD|A_STANDOUT|A_BLINK|A_DIM|A_UNDERLINE|A_INVIS|A_REVERSE))

static void
init_wchar_pieces ()
{
  w_pawn_wchar = str_to_wchar (config.utf8_pieces ? "♙" : "P");
  w_rook_wchar = str_to_wchar (config.utf8_pieces ? "♖" : "R");
  w_bishop_wchar = str_to_wchar (config.utf8_pieces ? "♗" : "B");
  w_knight_wchar = str_to_wchar (config.utf8_pieces ? "♘" : "N");
  w_queen_wchar = str_to_wchar (config.utf8_pieces ? "♕" : "Q");
  w_king_wchar = str_to_wchar (config.utf8_pieces ? "♔" : "K");
  b_pawn_wchar = str_to_wchar (config.utf8_pieces ? "♟" : "p");
  b_rook_wchar = str_to_wchar (config.utf8_pieces ? "♜" : "r");
  b_bishop_wchar = str_to_wchar (config.utf8_pieces ? "♝" : "b");
  b_knight_wchar = str_to_wchar (config.utf8_pieces ? "♞" : "n");
  b_queen_wchar = str_to_wchar (config.utf8_pieces ? "♛" : "q");
  b_king_wchar = str_to_wchar (config.utf8_pieces ? "♚" : "k");
  empty_wchar = str_to_wchar (" ");
  enpassant_wchar = str_to_wchar ("x");
}

static wchar_t *
piece_to_wchar (unsigned char p)
{
  switch (p)
    {
    case 'P':
      return w_pawn_wchar;
    case 'p':
      return b_pawn_wchar;
    case 'R':
      return w_rook_wchar;
    case 'r':
      return b_rook_wchar;
    case 'B':
      return w_bishop_wchar;
    case 'b':
      return b_bishop_wchar;
    case 'N':
      return w_knight_wchar;
    case 'n':
      return b_knight_wchar;
    case 'Q':
      return w_queen_wchar;
    case 'q':
      return b_queen_wchar;
    case 'K':
      return w_king_wchar;
    case 'k':
      return b_king_wchar;
    case 'x':
      return enpassant_wchar;
    }

  return empty_wchar;
}

static int piece_can_attack (GAME g, int rank, int file)
{
    struct userdata_s *d = g->data;
    char *m, *frfr = NULL;
    pgn_error_t e;
    int row, col, p, v, pi, cpi;

    if (d->rotate) {
        rotate_position(&d->c_row, &d->c_col);
        rotate_position(&d->sp.srow, &d->sp.scol);
    }

    v = d->b[RANKTOBOARD (d->c_row)][FILETOBOARD (d->c_col)].valid;
    pi = pgn_piece_to_int (d->b[RANKTOBOARD (rank)][FILETOBOARD (file)].icon);
    cpi = d->sp.icon
	? pgn_piece_to_int (d->b[RANKTOBOARD (d->sp.srow)][FILETOBOARD (d->sp.scol)].icon)
	: pgn_piece_to_int (d->b[RANKTOBOARD (d->c_row)][FILETOBOARD (d->c_col)].icon);

    if (pi == OPEN_SQUARE || cpi == OPEN_SQUARE || !VALIDFILE (file)
	|| !VALIDRANK (rank)) {
	if (d->rotate) {
            rotate_position(&d->c_row, &d->c_col);
            rotate_position(&d->sp.srow, &d->sp.scol);
	}

        return 0;
    }

    if (d->sp.icon) {
	col = v ? d->c_col : d->sp.scol;
	row = v ? d->c_row : d->sp.srow;
    }
    else {
	col = d->c_col;
	row = d->c_row;
    }

    m = malloc(MAX_SAN_MOVE_LEN+1);
    m[0] = INTTOFILE (file);
    m[1] = INTTORANK (rank);
    m[2] = INTTOFILE (col);
    m[3] = INTTORANK (row);
    m[4] = 0;

    if (d->sp.icon && v) {
        BOARD b;

	memcpy (b, d->b, sizeof(BOARD));
	p = b[RANKTOBOARD (d->sp.srow)][FILETOBOARD (d->sp.scol)].icon;
	b[RANKTOBOARD (d->sp.srow)][FILETOBOARD (d->sp.scol)].icon =
	  pgn_int_to_piece (WHITE, OPEN_SQUARE);
	b[RANKTOBOARD (row)][FILETOBOARD (col)].icon = p;
	pgn_switch_turn(g);
	e = pgn_validate_move (g, b, &m, &frfr);
	pgn_switch_turn (g);
	free (m);
	free (frfr);

	if (e != E_PGN_OK && pgn_piece_to_int (d->sp.icon) == PAWN) {
	    int n = (d->sp.srow == 7 && rank == 5) ? 6 :
		(d->sp.srow == 2 && rank == 4) ? 3 : 0;

	    if (n && (file == d->c_col-1 || file == d->c_col+1)) {
		memcpy (b, d->b, sizeof(BOARD));
		p = b[RANKTOBOARD (d->sp.srow)][FILETOBOARD (d->sp.scol)].icon;
		b[RANKTOBOARD (d->sp.srow)][FILETOBOARD (d->sp.scol)].icon =
		    pgn_int_to_piece (WHITE, OPEN_SQUARE);
		b[RANKTOBOARD (row)][FILETOBOARD (col)].icon = p;
		b[RANKTOBOARD (n)][FILETOBOARD (d->sp.scol)].enpassant = 1;
		m = malloc(MAX_SAN_MOVE_LEN+1);
		m[0] = INTTOFILE (file);
		m[1] = INTTORANK (rank);
		m[2] = INTTOFILE (col);
		m[3] = INTTORANK (n);
		m[4] = 0;
		pgn_switch_turn(g);
		SET_FLAG (g->flags, GF_ENPASSANT);
		e = pgn_validate_move (g, b, &m, &frfr);
		CLEAR_FLAG (g->flags, GF_ENPASSANT);
		pgn_switch_turn (g);
		free (m);
		free (frfr);
	    }
	}

	goto pca_quit;
    }

    pgn_switch_turn(g);
    e = pgn_validate_move (g, d->b, &m, &frfr);
    pgn_switch_turn (g);

    if (!strcmp (m, "O-O") || !strcmp (m, "O-O-O"))
        e = E_PGN_INVALID;

    if (e == E_PGN_OK) {
        int sf = FILETOINT (frfr[0]), sr = RANKTOINT (frfr[1]);
	int df = FILETOINT (frfr[2]);

	pi = d->b[RANKTOBOARD (sr)][FILETOBOARD (sf)].icon;
	pi = pgn_piece_to_int (pi);
	if (pi == PAWN && sf == df)
	    e = E_PGN_INVALID;
    }

    free (m);
    free (frfr);

pca_quit:
    if (d->rotate) {
        rotate_position(&d->c_row, &d->c_col);
	rotate_position(&d->sp.srow, &d->sp.scol);
    }

    return e == E_PGN_OK ? 1 : 0;
}

void print_piece(WINDOW *w, int l, int c, char p)
{
    int i, y, ff = 0;

    for (i = 0; i < 13; i += 2) {
        if (p == piece_chars[i] || p == piece_chars[i + 1]) {
	    for (y = 0; y < 3; y++)
	        mvwprintw(w, l + y, c, "%s", f_pieces[i + ff + y]);
	    return;
	}

	ff++;
    }

    for (y = 0; y < 3; y++)
        mvwprintw(w, l + y, c, f_pieces[0]);
}

void board_prev_move_play (GAME g)
{
  struct userdata_s *d = g->data;
  char l = strlen(d->pm_frfr);

  if (l) {
      char q = (l > 4) ? 2 : 1;

      d->pm_row = RANKTOINT(d->pm_frfr[l - q++]);
      d->pm_col = FILETOINT(d->pm_frfr[l - q++]);
      d->ospm_row = RANKTOINT(d->pm_frfr[l - q++]);
      d->ospm_col = FILETOINT(d->pm_frfr[l - q]);
      if (d->rotate) {
          rotate_position(&d->pm_row, &d->pm_col);
          rotate_position(&d->ospm_row, &d->ospm_col);
      }
  }
  else {
      d->pm_row = 0;
      d->pm_col = 0;
      d->ospm_row = 0;
      d->ospm_col = 0;
  }
}

void board_prev_move_history (GAME g)
{
  struct userdata_s *d = g->data;

  if (g->hindex) {
      char *move = g->hp[g->hindex - 1]->move;

      if (move) {
          if (d->mode == MODE_PLAY)
            coordofmove(g, move, &d->pm_row, &d->pm_col);
          else {
              d->pm_row = 0;
              d->pm_col = 0;
          }

          if (*move == 'O') {
              d->ospm_row = g->turn == WHITE ? 8 : 1;
              d->ospm_col = 5;
              return;
          }

          BOARD ob;
          unsigned char f, r;

          pgn_board_init(ob);

          if (g->hindex > 1) {
              HISTORY *h = pgn_history_by_n(g->hp, g->hindex - 2);
              if (h) {
                  pgn_board_init_fen(g, ob, h->fen);
                  pgn_switch_turn(g);
              }
          }

          for (f = 0; f < 8; f++) {
              for (r = 0; r < 8; r++) {
                  if (ob[f][r].icon != '.' && d->b[f][r].icon == '.') {
                      d->ospm_row = INV_INT0(f) + 1;
                      d->ospm_col = r + 1;
                      break;
                  }
              }
          }

          if (d->rotate) {
              if (d->mode == MODE_PLAY)
                  rotate_position(&d->pm_row, &d->pm_col);

              rotate_position(&d->ospm_row, &d->ospm_col);
          }

          return;
      }
  }
  else {
      d->ospm_row = 0;
      d->ospm_col = 0;
      d->pm_row = 0;
      d->pm_col = 0;
  }
}

static int is_the_square (int brow, int bcol, int row, int col,
			int prow, int pcol)
{
    if ((!BIG_BOARD && row == ROWTOMATRIX(prow) && col == COLTOMATRIX(pcol))
        || (BIG_BOARD && brow + 1 == INV_INT(prow) && bcol + 1 == pcol))
	return 1;

    return 0;
}

static int is_prev_move (struct userdata_s *d, int brow, int bcol,
			 int row, int col)
{
    if (is_the_square (brow, bcol, row, col, d->pm_row, d->pm_col))
        return 1;

    return 0;
}

void update_board_window(GAME g)
{
    int row, col;
    int bcol = 0, brow = 0;
    int l = config.coordsyleft;
    int maxy = BOARD_HEIGHT, maxx = BOARD_WIDTH;
    int ncols = 0, offset = 1;
    int rowr = (MEGA_BOARD) ? 6 : (BIG_BOARD) ? 4 : 2;
    int colr = (MEGA_BOARD) ? 12 : (BIG_BOARD) ? 8 : 4;
    unsigned coords_y = 8, cxgc = 0;
    unsigned i, cpd = 0;
    struct userdata_s *d = g->data;

    if (config.bprevmove && d->mode != MODE_EDIT) {
        if (!d->pm_undo && d->mode == MODE_PLAY)
            board_prev_move_play(g);
        else
            board_prev_move_history(g);
    }
    else {
        d->pm_row = 0;
        d->pm_col = 0;
        d->ospm_row = 0;
        d->ospm_col = 0;
    }

    if (d->mode != MODE_PLAY && d->mode != MODE_EDIT)
	update_cursor(g, g->hindex);

    if (BIG_BOARD) {
	if (d->rotate) {
	    brow = 7;
	    coords_y = 1;
	}
    }
    else {
        if (d->rotate) {
	    brow = 1;
	    coords_y = 1;
	}
	else
	    brow = 8;
    }

    for (row = 0; row < maxy; row++) {
        if (BIG_BOARD) {
	    if (d->rotate)
	        bcol = 7;
	    else
	        bcol = 0;
	}
	else {
	    if (d->rotate)
	        bcol = 8;
	    else
	        bcol = 1;
	}

	for (col = 0; col < maxx; col++) {
	    int attrwhich = -1;
	    chtype attrs = 0, old_attrs = 0;
	    unsigned char p;
	    int can_attack = 0;
	    int valid = 0;

	    if (row == 0 || row == maxy - 2) {
		if (col == 0)
		    mvwaddch(boardw, row, col + l,
			     LINE_GRAPHIC((row)
					  ? ACS_LLCORNER | CP_BOARD_GRAPHICS
					  : ACS_ULCORNER | CP_BOARD_GRAPHICS));
		else if (col == maxx - 2)
		    mvwaddch(boardw, row, col + l,
			     LINE_GRAPHIC((row)
					  ? ACS_LRCORNER | CP_BOARD_GRAPHICS
					  : ACS_URCORNER | CP_BOARD_GRAPHICS));
		else if (!(col % colr))
		    mvwaddch(boardw, row, col + l,
			     LINE_GRAPHIC((row)
					  ? ACS_BTEE | CP_BOARD_GRAPHICS
					  : ACS_TTEE | CP_BOARD_GRAPHICS));
		else {
		    if (col != maxx - 1)
			mvwaddch(boardw, row, col + l,
				LINE_GRAPHIC(ACS_HLINE | CP_BOARD_GRAPHICS));
		}

		continue;
	    }

	    if ((row % 2) && col == maxx - 1 &&
		(coords_y > 0 && coords_y < 9)) {
		wattron(boardw, CP_BOARD_COORDS);
			mvwprintw(boardw,
				  (BIG_BOARD) ? row * ((MEGA_BOARD) ? 3 : 2)
				  : row, (l) ? 0 : col, "%d",
				  (d->rotate) ? coords_y++ : coords_y--);
		wattroff(boardw, CP_BOARD_COORDS);
		continue;
	    }

	    if ((col == 0 || col == maxx - 2) && row != maxy - 1) {
		if (!(row % rowr))
		    mvwaddch(boardw, row, col + l,
			    LINE_GRAPHIC((col) ?
				ACS_RTEE | CP_BOARD_GRAPHICS :
				ACS_LTEE | CP_BOARD_GRAPHICS));
		else
		    mvwaddch(boardw, row, col + l,
			    LINE_GRAPHIC(ACS_VLINE | CP_BOARD_GRAPHICS));

		continue;
	    }

	    if ((row % rowr) && !(col % colr) && row != maxy - 1) {
		mvwaddch(boardw, row, col + l,
			LINE_GRAPHIC(ACS_VLINE | CP_BOARD_GRAPHICS));
		continue;
	    }

	    if (!(col % colr) && row != maxy - 1) {
		mvwaddch(boardw, row, col + l,
			LINE_GRAPHIC(ACS_PLUS | CP_BOARD_GRAPHICS));
		continue;
	    }

	    if ((row % rowr)) {
		if ((col % colr)) {
		    if (BIG_BOARD)
		        attrwhich = (cb[brow][bcol]) ? WHITE : BLACK;
		    else {
		        if (ncols++ == 8) {
			  offset++;
			  ncols = 1;
			}

			if (((ncols % 2) && !(offset % 2))
			    || (!(ncols % 2) && (offset % 2)))
			    attrwhich = BLACK;
			else
			    attrwhich = WHITE;
		    }

		    if (BIG_BOARD && d->rotate) {
		        brow = INV_INT0(brow);
			bcol = INV_INT0(bcol);
		    }

		    if (BIG_BOARD)
		        p = d->b[brow][bcol].icon;
		    else
		        p = d->b[RANKTOBOARD (brow)][FILETOBOARD (bcol)].icon;

		    int pi = pgn_piece_to_int(p);

		    if (config.details &&
			((!BIG_BOARD && d->b[RANKTOBOARD (brow)][FILETOBOARD (bcol)].enpassant)
			 || (BIG_BOARD && d->b[brow][bcol].enpassant))) {
		        p = pi = 'x';
			attrs = mix_cp(CP_BOARD_ENPASSANT,
				       (attrwhich == WHITE) ? CP_BOARD_WHITE : CP_BOARD_BLACK,
				       ATTRS(CP_BOARD_ENPASSANT), A_FG_B_BG);
		    }

		    if (config.showattacks && config.details
			&& piece_can_attack (g,
					     BIG_BOARD ? INV_INT0(brow)+1 : brow,
					     BIG_BOARD ? bcol+1 : bcol)) {
			    attrs = CP_BOARD_ATTACK;
			    old_attrs = attrs;
			    can_attack = 1;
		    }

		    if (config.validmoves &&
			((!BIG_BOARD && d->b[RANKTOBOARD (brow)][FILETOBOARD (bcol)].valid)
			 || (BIG_BOARD && d->b[brow][bcol].valid))) {
		        old_attrs = -1;
			valid = 1;

			if (attrwhich == WHITE)
			    attrs = mix_cp(CP_BOARD_MOVES_WHITE,
					   IS_ENPASSANT(p),
					   ATTRS(CP_BOARD_MOVES_WHITE),
					   B_FG_A_BG);
			else
			    attrs = mix_cp(CP_BOARD_MOVES_BLACK,
					   IS_ENPASSANT(p),
					   ATTRS(CP_BOARD_MOVES_BLACK),
					   B_FG_A_BG);
		    }
		    else if (p != 'x' && !can_attack)
			attrs = (attrwhich == WHITE) ? CP_BOARD_WHITE : CP_BOARD_BLACK;

                    if (BIG_BOARD && d->rotate) {
                        brow = INV_INT0(brow);
                        bcol = INV_INT0(bcol);
                    }

                    if (is_the_square (brow, bcol, row, col, d->c_row,
                                       d->c_col)) {
                        attrs = mix_cp(CP_BOARD_CURSOR, IS_ENPASSANT(p),
                                       ATTRS(CP_BOARD_CURSOR), B_FG_A_BG);
                        old_attrs = -1;
                    }
                    else if (is_the_square (brow, bcol, row, col,
                                            d->sp.srow, d->sp.scol)) {
                        attrs = mix_cp(CP_BOARD_SELECTED, IS_ENPASSANT(p),
                                       ATTRS(CP_BOARD_SELECTED), B_FG_A_BG);
                        old_attrs = -1;
                    }
		    else if ((is_prev_move (d, brow, bcol, row, col) && !valid)
                             || (is_the_square (brow, bcol, row, col,
                                                d->ospm_row, d->ospm_col))) {
			attrs = mix_cp(CP_BOARD_PREVMOVE, IS_ENPASSANT(p),
				       ATTRS(CP_BOARD_PREVMOVE), B_FG_A_BG);
			old_attrs = -1;
		    }

		    if (row == maxy - 1)
			attrs = 0;

		    if (can_attack) {
			int n = is_prev_move (d, brow, bcol, row, col);
			chtype a = n && !valid
			    ? CP_BOARD_PREVMOVE : attrwhich == WHITE ? valid ? CP_BOARD_MOVES_WHITE : CP_BOARD_WHITE : valid ? CP_BOARD_MOVES_BLACK : CP_BOARD_BLACK;
			attrs = mix_cp(CP_BOARD_ATTACK, a,
				       ATTRS (CP_BOARD_ATTACK), A_FG_B_BG);
			old_attrs = -1;
		    }

		    if (BIG_BOARD)
		        wmove(boardw, row, col + ((MEGA_BOARD) ? 5 : 3) + l);
		    else
		        mvwaddch(boardw, row, col + l, ' ' | attrs);

		    if (row == maxy - 1 && cxgc < 8) {
		        waddch(boardw, "abcdefgh"[(BIG_BOARD) ? bcol : bcol - 1] | CP_BOARD_COORDS);
			cxgc++;
		    }
		    else {
			if (old_attrs == -1) {
			    old_attrs = attrs;
			    goto printc;
			}

			old_attrs = attrs;

			if (pi != OPEN_SQUARE && p != 'x' && !can_attack) {
			    if (attrwhich == WHITE) {
				if (isupper(p))
				    attrs = CP_BOARD_W_W;
				else
				    attrs = CP_BOARD_W_B;
			    }
			    else {
				if (isupper(p))
				    attrs = CP_BOARD_B_W;
				else
				    attrs = CP_BOARD_B_B;
			    }
			}

printc:
			if (BIG_BOARD) {
			    if (config.details && !can_attack
				&& castling_state(g, d->b,
				(d->rotate) ? INV_INT(brow + 1) - 1: brow,
				(d->rotate) ? INV_INT(bcol + 1) - 1: bcol, p, 0))
			        attrs = mix_cp(CP_BOARD_CASTLING, attrs,
					       ATTRS(CP_BOARD_CASTLING),
					       A_FG_B_BG);
			}
			else {
			    if (config.details && !can_attack
				&& castling_state(g, d->b, RANKTOBOARD (brow),
						  FILETOBOARD (bcol), p, 0)) {
			         attrs = mix_cp(CP_BOARD_CASTLING, attrs,
						ATTRS(CP_BOARD_CASTLING),
						A_FG_B_BG);
			    }
			}

			if (BIG_BOARD) {
			  // FIXME: Reimpresión de piezas(+4).
			    if (cpd < 67) {
				wattron (boardw, attrs);
				if (MEGA_BOARD){
				    for (i = 0; i < 5; i++)
				        mvwprintw(boardw, i + brow * 6 + 1,
						  bcol * 12 + 1 + l,
						  "           ");
				    if (pi != OPEN_SQUARE)
				        print_piece(boardw, brow * 6 + 2,
						    bcol * 12 + 3 + l, p);
				}
				else {
				    print_piece(boardw, brow * 4 + 1,
						bcol * 8 + 1 + l,
						(pi != OPEN_SQUARE) ? p : 0);
				}

				wattroff (boardw, attrs);
				cpd++;
			    }
			}
			else {
			    wattron (boardw, attrs);
			    waddwstr (boardw, piece_to_wchar (pi != OPEN_SQUARE ? p : 0));
			    wattroff (boardw, attrs);
			}

			attrs = old_attrs;
		    }

		    if (BIG_BOARD)
		        col += (MEGA_BOARD) ? 10 : 6;
		    else {
		        waddch(boardw, ' ' | attrs);
			col += 2;
		    }

		    if (d->rotate)
			bcol--;
		    else
			bcol++;

		    if (BIG_BOARD) {
		        if (bcol > 7)
			    bcol = 0;
			if (bcol < 0)
			    bcol = 7;
		    }
		}
	    }
	    else {
		if (col != maxx - 1)
		    mvwaddch(boardw, row, col + l,
			    LINE_GRAPHIC(ACS_HLINE | CP_BOARD_GRAPHICS));
	    }
	}

	if (row % rowr) {
	    if (d->rotate)
		brow++;
	    else
		brow--;
	}

	if (BIG_BOARD) {
	    if (brow > 7)
	        brow = 0;
	    if (brow < 0)
	        brow = 7;
	}
    }
}

void invalid_move(int n, int e, const char *m)
{
    if (curses_initialized)
	cmessage(ERROR_STR, ANY_KEY_STR, "%s \"%s\" (round #%i)", (e == E_PGN_AMBIGUOUS)
		? _("Ambiguous move") : _("Invalid move"), m, n);
    else
	warnx("%s: %s \"%s\" (round #%i)", loadfile, (e == E_PGN_AMBIGUOUS)
		? _("Ambiguous move") : _("Invalid move"), m, n);
}

void gameover(GAME g)
{
    struct userdata_s *d = g->data;

    SET_FLAG(g->flags, GF_GAMEOVER);
    d->mode = MODE_HISTORY;
    stop_engine(g);
}

static void update_clock(GAME g, struct itimerval it)
{
    struct userdata_s *d = g->data;

    if (TEST_FLAG(d->flags, CF_CLOCK) && g->turn == WHITE) {
	d->wclock.elapsed.tv_sec += it.it_value.tv_sec;
	d->wclock.elapsed.tv_usec += it.it_value.tv_usec;

	if (d->wclock.elapsed.tv_usec > 1000000 - 1) {
	    d->wclock.elapsed.tv_sec += d->wclock.elapsed.tv_usec / 1000000;
	    d->wclock.elapsed.tv_usec = d->wclock.elapsed.tv_usec % 1000000;
	}

	if (d->wclock.tc[d->wclock.tcn][1] &&
		d->wclock.elapsed.tv_sec >= d->wclock.tc[d->wclock.tcn][1]) {
	    pgn_tag_add(&g->tag, "Result", "0-1");
	    gameover(g);
	}
    }
    else if (TEST_FLAG(d->flags, CF_CLOCK) && g->turn == BLACK) {
	d->bclock.elapsed.tv_sec += it.it_value.tv_sec;
	d->bclock.elapsed.tv_usec += it.it_value.tv_usec;

	if (d->bclock.elapsed.tv_usec > 1000000 - 1) {
	    d->bclock.elapsed.tv_sec += d->bclock.elapsed.tv_usec / 1000000;
	    d->bclock.elapsed.tv_usec = d->bclock.elapsed.tv_usec % 1000000;
	}

	if (d->bclock.tc[d->bclock.tcn][1] &&
		d->bclock.elapsed.tv_sec >= d->bclock.tc[d->bclock.tcn][1]) {
	    pgn_tag_add(&g->tag, "Result", "1-0");
	    gameover(g);
	}
    }

    d->elapsed.tv_sec += it.it_value.tv_sec;
    d->elapsed.tv_usec += it.it_value.tv_usec;

    if (d->elapsed.tv_usec > 1000000 - 1) {
	d->elapsed.tv_sec += d->elapsed.tv_usec / 1000000;
	d->elapsed.tv_usec = d->elapsed.tv_usec % 1000000;
    }
}

static void update_time_control(GAME g)
{
    struct userdata_s *d = g->data;
    struct clock_s *clk = (g->turn == WHITE) ? &d->wclock : &d->bclock;

    if (clk->incr)
	clk->tc[clk->tcn][1] += clk->incr;

    if (!clk->tc[clk->tcn][1])
	return;

    clk->move++;

    if (!clk->tc[clk->tcn][0] || clk->move >= clk->tc[clk->tcn][0]) {
	clk->move = 0;
	clk->tc[clk->tcn + 1][1] += abs(clk->elapsed.tv_sec - clk->tc[clk->tcn][1]);
	memset(&clk->elapsed, 0, sizeof(clk->elapsed));
	clk->tcn++;
    }
}

void update_history_window(GAME g)
{
    char buf[HISTORY_WIDTH - 1];
    HISTORY *h = NULL;
    int n, total;
    int t = pgn_history_total(g->hp);

    n = (g->hindex + 1) / 2;

    if (t % 2)
	total = (t + 1) / 2;
    else
	total = t / 2;

    if (t)
	snprintf(buf, sizeof(buf), "%u %s %u%s", n, _("of"), total,
		(movestep == 1) ? _(" (ply)") : "");
    else
	strncpy(buf, _("not available"), sizeof(buf)-1);

    buf[sizeof(buf)-1] = 0;
    mvwprintw(historyw, 2, 1, "%*s %-*s", 10, _("Move:"),
	    HISTORY_WIDTH - 14, buf);

    h = pgn_history_by_n(g->hp, g->hindex);
    snprintf(buf, sizeof(buf), "%s",
	     (h && h->move) ? h->move
	     : (LINES < 24) ? _("empty") : _("not available"));
    n = 0;

    if (h && ((h->comment) || h->nag[0])) {
        strncat(buf, _(" (Annotated"), sizeof(buf)-1);
	n++;
    }

    if (h && h->rav) {
	strncat(buf, (n) ? ",+" : " (+", sizeof(buf)-1);
	n++;
    }

    if (g->ravlevel) {
	strncat(buf, (n) ? ",-" : " (-", sizeof(buf)-1);
	n++;
    }

    if (n)
	strncat(buf, ")", sizeof(buf)-1);

    mvwprintw(historyw, 3, ((LINES < 24) ? 17 : 1), "%s %-*s",
	      (LINES < 24) ? _("Next:") :_("Next move:"),
	      HISTORY_WIDTH - ((LINES < 24) ? 26 : 14), buf);

    h = pgn_history_by_n(g->hp, g->hindex - 1);
    snprintf(buf, sizeof(buf), "%s",
	     (h && h->move) ? h->move
	     : (LINES < 24) ? _("empty") : _("not available"));
    n = 0;

    if (h && ((h->comment) || h->nag[0])) {
        strncat(buf, _(" (Annotated"), sizeof(buf)-1);
	n++;
    }

    if (h && h->rav) {
	strncat(buf, (n) ? ",+" : " (+", sizeof(buf)-1);
	n++;
    }

    if (g->ravlevel) {
	strncat(buf, (n) ? ",-" : " (-", sizeof(buf)-1);
	n++;
    }

    if (n)
	strncat(buf, ")", sizeof(buf)-1);

    mvwprintw(historyw, ((LINES < 24) ? 3 : 4), 1, "%s %-*s",
	      (LINES < 24) ? _("Prev.:") : _("Prev move:"),
	      HISTORY_WIDTH - ((LINES < 24) ? 26 : 14), buf);
}

void do_validate_move(char **move)
{
    struct userdata_s *d = gp->data;
    int n;
    char *frfr = NULL;

    if (TEST_FLAG(d->flags, CF_HUMAN)) {
	if ((n = pgn_parse_move(gp, d->b, move, &frfr)) != E_PGN_OK) {
	    invalid_move(d->n + 1, n, *move);
	    return;
	}

	strcpy(d->pm_frfr, frfr);
	update_time_control(gp);
	pgn_history_add(gp, d->b, *move);
	pgn_switch_turn(gp);
    }
    else {
	if ((n = pgn_validate_move(gp, d->b, move, &frfr)) != E_PGN_OK) {
	    invalid_move(d->n + 1, n, *move);
	    return;
	}

	add_engine_command(gp, ENGINE_THINKING, "%s\n",
			   (config.engine_protocol == 1) ? frfr : *move);
    }

    d->sp.srow = d->sp.scol = d->sp.icon = 0;

    if (config.validmoves)
	pgn_reset_valid_moves(d->b);

    if (TEST_FLAG(gp->flags, GF_GAMEOVER))
	d->mode = MODE_HISTORY;
    else
	SET_FLAG(d->flags, CF_MODIFIED);

    free (frfr);
    d->paused = 0;
    update_history_window(gp);
    update_board_window(gp);
    return;
}

void do_promotion_piece_finalize(WIN *win)
{
    char *p, *str = win->data;

    if (pgn_piece_to_int(win->c) == -1)
	return;

    p = str + strlen(str);
    *p++ = toupper(win->c);
    *p = '\0';
    do_validate_move(&str);
    free (str);
    win->data = NULL;
}

static void move_to_engine(GAME g)
{
    struct userdata_s *d = g->data;
    char *str;
    int piece;

    if (config.validmoves &&
	!d->b[RANKTOBOARD(d->sp.row)][FILETOBOARD(d->sp.col)].valid)
	return;

    str = Malloc(MAX_SAN_MOVE_LEN + 1);
    snprintf(str, MAX_SAN_MOVE_LEN + 1, "%c%i%c%i",
	     _("abcdefgh")[d->sp.scol - 1],
	     d->sp.srow, _("abcdefgh")[d->sp.col - 1], d->sp.row);

    piece = pgn_piece_to_int(d->b[RANKTOBOARD(d->sp.srow)][FILETOBOARD(d->sp.scol)].icon);

    if (piece == PAWN && (d->sp.row == 8 || d->sp.row == 1)) {
      construct_message(_("Select Pawn Promotion Piece"), _ ("R/N/B/Q"), 1, 1, NULL, NULL,
		str, do_promotion_piece_finalize, 0, 0, "%s", _("R = Rook, N = Knight, B = Bishop, Q = Queen"));
	return;
    }

    do_validate_move(&str);
    free (str);
}

static char *clock_to_char(long n)
{
    static char buf[16];
    int h = 0, m = 0, s = 0;

    h = n / 3600;
    m = (n % 3600) / 60;
    s = (n % 3600) % 60;
    snprintf(buf, sizeof(buf), "%.2i:%.2i:%.2i", h, m, s);
    return buf;
}

static char *timeval_to_char(struct timeval t, long limit)
{
    static char buf[9];
    int h = 0, m = 0, s = 0;
    int n = limit ? abs(limit - t.tv_sec) : 0;

    h = n / 3600;
    m = (n % 3600) / 60;
    s = (n % 3600) % 60;
    snprintf(buf, sizeof(buf), "%.2i:%.2i:%.2i", h, m, s);
    return buf;
}

static char *time_control_status(struct clock_s *clk)
{
    static char buf[80] = {0};

    buf[0] = 0;

    if (clk->tc[clk->tcn][0] && clk->tc[clk->tcn + 1][1])
	snprintf(buf, sizeof(buf), " M%.2i/%s", abs(clk->tc[clk->tcn][0] - clk->move),
		clock_to_char(clk->tc[clk->tcn + 1][1]));
    else if (!clk->incr)
	return "";

    if (clk->incr) {
        char buf[16];
	strncat(buf, " I", sizeof(buf)-1);
	strncat(buf, itoa(clk->incr, buf), sizeof(buf)-1);
    }

    return buf;
}

void update_status_window(GAME g)
{
    int i = 0;
    char *buf;
    char tmp[15] = {0}, *engine, *mode;
    char t[COLS];
    int w;
    char *p;
    int maxy, maxx;
    int len;
    struct userdata_s *d = g->data;
    int y;
    int n;

    if (!curses_initialized)
	return;

    getmaxyx(statusw, maxy, maxx);
    (void)maxy;
    w = maxx - 2 - 8;
    len = maxx - 2;
    buf = Malloc(len);
    y = 2;

    wchar_t *loadfilew =  loadfile[0] ? str_etc (loadfile, w, 1) : str_to_wchar (_ ("not available"));
    mvwprintw(statusw, y++, 1, "%*s %-*ls", 7, _("File:"), w, loadfilew);
    free (loadfilew);
    snprintf(buf, len, "%i %s %i", gindex + 1, _("of"), gtotal);
    mvwprintw(statusw, y++, 1, "%*s %-*s", 7, _("Game:"), w, buf);

    *tmp = '\0';
    p = tmp;

    if (config.details) {
	*p++ = 'D';
	i++;
    }

    if (TEST_FLAG(d->flags, CF_DELETE)) {
	if (i)
	    *p++ = '/';

	*p++ = 'X';
	i++;
    }

    if (TEST_FLAG(g->flags, GF_PERROR)) {
	if (i)
	    *p++ = '/';

	*p++ = '!';
	i++;
    }

    if (TEST_FLAG(d->flags, CF_MODIFIED)) {
	if (i)
	    *p++ = '/';

	*p++ = '*';
	i++;
    }

    pgn_config_get(PGN_STRICT_CASTLING, &n);

    if (n == 1) {
	if (i)
	    *p++ = '/';

	*p++ = 'C';
	i++;
    }
#ifdef WITH_LIBPERL
    if (TEST_FLAG(d->flags, CF_PERL)) {
	if (i)
	    *p++ = '/';

	*p++ = 'P';
	i++;
    }
#endif

    *p = '\0';
    mvwprintw(statusw, y++, 1, "%*s %-*s", 7, _("Flags:"), w, (tmp[0]) ? tmp : "-");

    switch (d->mode) {
	case MODE_HISTORY:
	    mode = _("move history");
	    break;
	case MODE_EDIT:
	    mode = _("edit");
	    break;
	case MODE_PLAY:
	    mode = _("play");
	    break;
	default:
	    mode = _("(empty value)");
	    break;
    }

    snprintf(buf, len - 1, "%*s %s", 7, _("Mode:"), mode);

    if (d->mode == MODE_PLAY) {
	if (TEST_FLAG(d->flags, CF_HUMAN))
	    strncat(buf, _(" (human/human)"), len - 1);
	else if (TEST_FLAG(d->flags, CF_ENGINE_LOOP))
	    strncat(buf, _(" (engine/engine)"), len - 1);
	else
	    strncat(buf, (d->play_mode == PLAY_EH) ?
		    _(" (engine/human)") : _(" (human/engine)"), len - 1);
    }

    buf[len-1] = 0;
    mvwprintw(statusw, y++, 1, "%-*s", len, buf);
    free(buf);

    if (d->engine) {
	switch (d->engine->status) {
	    case ENGINE_THINKING:
		engine = _("pondering...");
		break;
	    case ENGINE_READY:
		engine = _("ready");
		break;
	    case ENGINE_INITIALIZING:
		engine = _("initializing...");
		break;
	    case ENGINE_OFFLINE:
		engine = _("offline");
		break;
	    default:
		engine = _("(empty value)");
		break;
	}
    }
    else
	engine = _("offline");

    mvwprintw(statusw, y, 1, "%*s %-*s", 7, _("Engine:"), w, " ");
    wattron(statusw, CP_STATUS_ENGINE);
    mvwaddstr(statusw, y++, 9, engine);
    wattroff(statusw, CP_STATUS_ENGINE);

    mvwprintw(statusw, y++, 1, "%*s %-*s", 7, _("Turn:"), w,
	    (g->turn == WHITE) ? _("white") : _("black"));

    strncpy(tmp, _("white"), sizeof(tmp)-1);
    tmp[0] = toupper(tmp[0]);
    snprintf(t, sizeof(t), "%s%s",
	    timeval_to_char(d->wclock.elapsed, d->wclock.tc[d->wclock.tcn][1]),
	    time_control_status(&d->wclock));
    mvwprintw(statusw, y++, 1, "%*s: %-*s", 6, tmp, w, t);

    strncpy(tmp, _("black"), sizeof(tmp)-1);
    tmp[0] = toupper(tmp[0]);
    snprintf(t, sizeof(t), "%s%s",
	    timeval_to_char(d->bclock.elapsed, d->bclock.tc[d->bclock.tcn][1]),
	    time_control_status(&d->bclock));
    mvwprintw(statusw, y++, 1, "%*s: %-*s", 6, tmp, w, t);

    mvwprintw(statusw, y++, 1, "%*s %-*s", 7, _("Total:"), w,
	    clock_to_char(d->elapsed.tv_sec));

//	for (i = 0; i < STATUS_WIDTH; i++)
//	mvwprintw(stdscr, STATUS_HEIGHT, i, " ");

    if (!status.notify)
	status.notify = str_to_wchar(_("Type F1 for help"));

    wattron(stdscr, CP_STATUS_NOTIFY);
    for (i = (config.boardleft) ? BOARD_WIDTH : 0;
	 i < ((config.boardleft) ? COLS : STATUS_WIDTH); i++)
	mvwprintw(stdscr, STATUS_HEIGHT, i, " ");
    mvwprintw(stdscr, STATUS_HEIGHT, CENTERX(STATUS_WIDTH, status.notify)
	      + ((config.boardleft) ? BOARD_WIDTH : 0),
	      "%ls", status.notify);
    wattroff(stdscr, CP_STATUS_NOTIFY);
}

wchar_t *translate_tag_name(const char *tag)
{
    if (!strcmp (tag, "Event"))
        return str_to_wchar (translatable_tag_names[0]);
    else if (!strcmp (tag, "Site"))
        return str_to_wchar (translatable_tag_names[1]);
    else if (!strcmp (tag, "Date"))
        return str_to_wchar (translatable_tag_names[2]);
    else if (!strcmp (tag, "Round"))
        return str_to_wchar (translatable_tag_names[3]);
    else if (!strcmp (tag, "White"))
        return str_to_wchar (translatable_tag_names[4]);
    else if (!strcmp (tag, "Black"))
        return str_to_wchar (translatable_tag_names[5]);
    else if (!strcmp (tag, "Result"))
        return str_to_wchar (translatable_tag_names[6]);

    return str_to_wchar (tag);
}

void update_tag_window(TAG **t)
{
    int i, l, w;
    int namel = 0;

    for (i = 0; t[i]; i++) {
        wchar_t *namewc = translate_tag_name(t[i]->name);

	l = wcslen(namewc);
	free (namewc);
	if (l > namel)
	    namel = l;
    }

    w = TAG_WIDTH - namel - 4;

    for (i = 0; t[i] && i < TAG_HEIGHT - 3; i++) {
        wchar_t *namewc = translate_tag_name(t[i]->name);
	wchar_t *valuewc = str_etc(t[i]->value, w, 0);

	mvwprintw(tagw, (i + 2), 1, "%*ls: %-*ls", namel, namewc, w, valuewc);
	free (namewc);
	free (valuewc);
    }

    for (; i < TAG_HEIGHT - 3; i++)
	mvwprintw(tagw, (i + 2), 1, "%*s", namel + w + 2, " ");
}

void append_enginebuf(GAME g, char *line)
{
    int i = 0;
    struct userdata_s *d = g->data;

    if (d->engine->enginebuf)
	for (i = 0; d->engine->enginebuf[i]; i++);

    if (i >= LINES - 3) {
	free(d->engine->enginebuf[0]);

	for (i = 0; d->engine->enginebuf[i+1]; i++)
	    d->engine->enginebuf[i] = d->engine->enginebuf[i+1];

	d->engine->enginebuf[i] = strdup(line);
    }
    else {
	d->engine->enginebuf = Realloc(d->engine->enginebuf, (i + 2) * sizeof(char *));
	d->engine->enginebuf[i++] = strdup(line);
	d->engine->enginebuf[i] = NULL;
    }
}

void update_engine_window(GAME g)
{
    int i;
    struct userdata_s *d = g->data;

    wmove(enginew, 0, 0);
    wclrtobot(enginew);

    if (d->engine && d->engine->enginebuf) {
	for (i = 0; d->engine->enginebuf[i]; i++)
	    mvwprintw(enginew, i + 2, 1, "%s", d->engine->enginebuf[i]);
    }

    window_draw_title(enginew, _("Engine IO Window"), COLS, CP_MESSAGE_TITLE,
	    CP_MESSAGE_BORDER);
}

void update_all(GAME g)
{
    struct userdata_s *d = g->data;

    /*
     * In the middle of a macro. Don't update the screen.
     */
    if (macro_match != -1)
	return;

    wmove(boardw, ROWTOMATRIX(d->c_row), COLTOMATRIX(d->c_col));
    update_board_window(g);
    update_status_window(g);
    update_history_window(g);
    update_tag_window(g->tag);
    update_engine_window(g);
    update_panels();
    doupdate();
}

static void game_next_prev(GAME g, int n, int count)
{
    if (gtotal < 2)
	return;

    if (n == 1) {
	if (gindex + count > gtotal - 1) {
	    if (count != 1)
		gindex = gtotal - 1;
	    else
		gindex = 0;
	}
	else
	    gindex += count;
    }
    else {
	if (gindex - count < 0) {
	    if (count != 1)
		gindex = 0;
	    else
		gindex = gtotal - 1;
	}
	else
	    gindex -= count;
    }

    gp = game[gindex];
}

static void delete_game(int which)
{
    int i, w = which;
    struct userdata_s *d;

    for (i = 0; i < gtotal; i++) {
	d = game[i]->data;

	if (i == w || TEST_FLAG(d->flags, CF_DELETE)) {
	    int n;

	    free_userdata_once(game[i]);
	    pgn_free(game[i]);

	    for (n = i; n+1 < gtotal; n++)
		game[n] = game[n+1];

	    gtotal--;
	    i--;
	    w = -1;
	}
    }

    if (which != -1) {
	if (which + 1 >= gtotal)
	    gindex = gtotal - 1;
	else
	    gindex = which;
    }
    else
	gindex = gtotal - 1;

    gp = game[gindex];
    gp->hp = gp->history;
}

/*
 * FIXME find across multiple games.
 */
static int find_move_exp(GAME g, regex_t r, int which, int count)
{
    int i;
    int ret;
    char errbuf[255];
    int incr;
    int found;

    incr = (which == 0) ? -1 : 1;

    for (i = g->hindex + incr - 1, found = 0; ; i += incr) {
	if (i == g->hindex - 1)
	    break;

	if (i >= pgn_history_total(g->hp))
	    i = 0;
	else if (i < 0)
	    i = pgn_history_total(g->hp) - 1;

	// FIXME RAV
	ret = regexec(&r, g->hp[i]->move, 0, 0, 0);

	if (ret == 0) {
	    if (count == ++found) {
		return i + 1;
	    }
	}
	else {
	    if (ret != REG_NOMATCH) {
		regerror(ret, &r, errbuf, sizeof(errbuf));
		cmessage(_("Error Matching Regular Expression"), ANY_KEY_STR, "%s", errbuf);
		return -1;
	    }
	}
    }

    return -1;
}

static int toggle_delete_flag(int n)
{
    int i, x;
    struct userdata_s *d = game[n]->data;

    TOGGLE_FLAG(d->flags, CF_DELETE);
    gindex = n;

    for (i = x = 0; i < gtotal; i++) {
	d = game[i]->data;

	if (TEST_FLAG(d->flags, CF_DELETE))
	    x++;
    }

    if (x == gtotal) {
	cmessage(NULL, ANY_KEY_STR, "%s", _("Cannot delete last game."));
	d = game[n]->data;
	CLEAR_FLAG(d->flags, CF_DELETE);
	return 1;
    }

    return 0;
}

static int find_game_exp(char *str, int which, int count)
{
    char *nstr = NULL, *exp = NULL;
    regex_t nexp, vexp;
    int ret = -1;
    int g = 0;
    char buf[255] = {0}, *tmp;
    char errbuf[255];
    int found = 0;
    int incr = (which == 0) ? -(1) : 1;

    strncpy(buf, str, sizeof(buf)-1);
    tmp = buf;

    if (strstr(tmp, ":") != NULL) {
	nstr = strsep(&tmp, ":");

	if ((ret = regcomp(&nexp, nstr,
			REG_ICASE|REG_EXTENDED|REG_NOSUB)) != 0) {
	    regerror(ret, &nexp, errbuf, sizeof(errbuf));
	    cmessage(_("Error Compiling Regular Expression"), ANY_KEY_STR, "%s", errbuf);
	    ret = g = -1;
	    goto cleanup;
	}
    }

    exp = tmp;

    while (exp && *exp && isspace(*exp))
	exp++;

    if (exp == NULL)
	goto cleanup;

    if ((ret = regcomp(&vexp, exp, REG_EXTENDED|REG_NOSUB)) != 0) {
	regerror(ret, &vexp, errbuf, sizeof(errbuf));
	cmessage(_("Error Compiling Regular Expression"), ANY_KEY_STR, "%s", errbuf);
	ret = -1;
	goto cleanup;
    }

    ret = -1;

    for (g = gindex + incr, found = 0; ; g += incr) {
	int t;

	if (g == gtotal)
	    g = 0;
	else if (g < 0)
	    g = gtotal - 1;

	if (g == gindex)
	    break;

	for (t = 0; game[g]->tag[t]; t++) {
	    if (nstr) {
		if (regexec(&nexp, game[g]->tag[t]->name, 0, 0, 0) == 0) {
		    if (regexec(&vexp, game[g]->tag[t]->value, 0, 0, 0) == 0) {
			if (count == ++found) {
			    ret = g;
			    goto cleanup;
			}
		    }
		}
	    }
	    else {
		if (regexec(&vexp, game[g]->tag[t]->value, 0, 0, 0) == 0) {
		    if (count == ++found) {
			ret = g;
			goto cleanup;
		    }
		}
	    }
	}

	ret = -1;
    }

cleanup:
    if (nstr)
	regfree(&nexp);

    if (g != -1)
	regfree(&vexp);

    return ret;
}

/*
 * Updates the notification line in the status window then refreshes the
 * status window.
 */
void update_status_notify(GAME g, char *fmt, ...)
{
    va_list ap;
#ifdef HAVE_VASPRINTF
    char *line;
#else
    char line[COLS];
#endif

    free(status.notify);
    status.notify = NULL;

    if (!fmt)
	return;

    va_start(ap, fmt);
#ifdef HAVE_VASPRINTF
    vasprintf(&line, fmt, ap);
#else
    vsnprintf(line, sizeof(line), fmt, ap);
#endif
    va_end(ap);

    status.notify = str_to_wchar(line);

#ifdef HAVE_VASPRINTF
    free(line);
#endif
}

int rav_next_prev(GAME g, BOARD b, int n)
{
    // Next RAV.
    if (n) {
	if ((!g->ravlevel && g->hindex && g->hp[g->hindex - 1]->rav == NULL) ||
		(!g->ravlevel && !g->hindex && g->hp[g->hindex]->rav == NULL) ||
		(g->ravlevel && g->hp[g->hindex]->rav == NULL))
	    return 1;

	g->rav = Realloc(g->rav, (g->ravlevel + 1) * sizeof(RAV));
	g->rav[g->ravlevel].hp = g->hp;
	g->rav[g->ravlevel].flags = g->flags;
	g->rav[g->ravlevel].fen = pgn_game_to_fen(g, b);
	g->rav[g->ravlevel].hindex = g->hindex;
	g->hp = (!g->ravlevel) ? (g->hindex) ? g->hp[g->hindex - 1]->rav : g->hp[g->hindex]->rav : g->hp[g->hindex]->rav;
	g->hindex = 0;
	g->ravlevel++;
	pgn_board_update(g, b, g->hindex + 1);
	return 0;
    }

    if (g->ravlevel - 1 < 0)
	return 1;

    // Previous RAV.
    g->ravlevel--;
    pgn_board_init_fen(g, b, g->rav[g->ravlevel].fen);
    free(g->rav[g->ravlevel].fen);
    g->hp = g->rav[g->ravlevel].hp;
    g->flags = g->rav[g->ravlevel].flags;
    g->hindex = g->rav[g->ravlevel].hindex;
    return 0;
}

static void draw_window_decor()
{
    move_panel(boardp, 0,
	       (config.boardleft) ? 0 : COLS - BOARD_WIDTH);
    move_panel(historyp, LINES - HISTORY_HEIGHT,
		(config.boardleft) ? (MEGA_BOARD) ? BOARD_WIDTH : 0 :
		(MEGA_BOARD) ? 0 : COLS - HISTORY_WIDTH);
    move_panel(statusp, 0,
	       (config.boardleft) ? BOARD_WIDTH : 0);
	move_panel(tagp, STATUS_HEIGHT + 1,
		(config.boardleft) ? (MEGA_BOARD) ? BOARD_WIDTH :
		HISTORY_WIDTH : 0);

    wbkgd(boardw, CP_BOARD_WINDOW);
    wbkgd(statusw, CP_STATUS_WINDOW);
    window_draw_title(statusw, _("Game Status"), STATUS_WIDTH,
	    CP_STATUS_TITLE, CP_STATUS_BORDER);
    wbkgd(tagw, CP_TAG_WINDOW);
    window_draw_title(tagw, _("Roster Tags"), TAG_WIDTH, CP_TAG_TITLE,
	    CP_TAG_BORDER);
    wbkgd(historyw, CP_HISTORY_WINDOW);
    window_draw_title(historyw, _("Move History"), HISTORY_WIDTH,
	    CP_HISTORY_TITLE, CP_HISTORY_BORDER);
}

void do_window_resize()
{
    if (LINES < 23 || COLS < 74)
	return;

    resizeterm(LINES, COLS);
    endwin();
    wresize(boardw, BOARD_HEIGHT, BOARD_WIDTH);
    wresize(historyw, HISTORY_HEIGHT, HISTORY_WIDTH);
    wresize(statusw, STATUS_HEIGHT, STATUS_WIDTH);
    wresize(tagw, TAG_HEIGHT, TAG_WIDTH);
    clear ();
    wclear (boardw);
    wclear (historyw);
    wclear (tagw);
    wclear (statusw);
    wclear (loadingw);
    wclear (enginew);
    draw_window_decor();
    update_all(gp);
    keypad(boardw, TRUE);
    curs_set(0);
    cbreak();
    noecho();
}

void do_global_redraw ()
{
    do_window_resize ();
}

void stop_clock()
{
    memset(&clock_timer, 0, sizeof(struct itimerval));
    setitimer(ITIMER_REAL, &clock_timer, NULL);
}

void start_clock(GAME g)
{
    struct userdata_s *d = g->data;

    if (clock_timer.it_interval.tv_usec)
	return;

    memset(&d->elapsed, 0, sizeof(struct timeval));
    clock_timer.it_value.tv_sec = 0;
    clock_timer.it_value.tv_usec = 100000;
    clock_timer.it_interval.tv_sec = 0;
    clock_timer.it_interval.tv_usec = 100000;
    setitimer(ITIMER_REAL, &clock_timer, NULL);
}

static void update_clocks()
{
    int i;
    struct userdata_s *d;
    struct itimerval it;
    int update = 0;

    getitimer(ITIMER_REAL, &it);

    for (i = 0; i < gtotal; i++) {
	d = game[i]->data;

	if (d && d->mode == MODE_PLAY) {
	    if (d->paused == 1 || TEST_FLAG(d->flags, CF_NEW))
		continue;
	    else if (d->paused == -1) {
		if (game[i]->side == game[i]->turn) {
		    d->paused = 1;
		    continue;
		}
	    }

	    update_clock(game[i], it);

	    if (game[i] == gp)
		update = 1;
	}
    }

    if (update) {
	update_status_window(gp);
	update_panels();
	doupdate();
    }
}

#define SKIP_SPACE(str) { while (isspace(*str)) str++; }

static int parse_clock_time(char **str)
{
    char *p = *str;
    int n = 0, t = 0;

    SKIP_SPACE(p);

    if (!isdigit(*p))
	return -1;

    while (*p) {
	if (isdigit(*p)) {
	    t = atoi(p);

	    while (isdigit(*p))
		p++;

	    continue;
	}

	switch (*p) {
	    case 'H':
	    case 'h':
		n += t * (60 * 60);
		t = 0;
		break;
	    case 'M':
	    case 'm':
		n += t * 60;
		t = 0;
		break;
	    case 'S':
	    case 's':
		n += t;
		t = 0;
		break;
	    case ' ':
		p++;
	    case '/':
	    case '+':
		goto done;
	    default:
		*str = p;
		return -1;
	}

	p++;
    }

done:
    n += t;
    *str = p;
    return n;
}

static int parse_clock_input(struct clock_s *clk, char *str, int *incr)
{
    char *p = str;
    long n = 0;
    int plus = 0;
    int m = 0;
    int tc = 0;

    SKIP_SPACE(p);

    if (!*p)
	return 0;

    if (*p == '+') {
	plus = 1;
	p++;
	SKIP_SPACE(p);

	if (*p == '+')
	    goto move_incr;
    }
    else
	memset(clk, 0, sizeof(struct clock_s));

again:
    /* Sudden death. */
    if (strncasecmp(p, "SD", 2) == 0) {
	n = 0;
	p += 2;
	goto tc;
    }

    n = parse_clock_time(&p);

    if (n == -1)
	return 1;

    if (!n)
	goto done;

    /* Time control. */
tc:
    if (*p == '/') {
	if (plus)
	    return 1;

	/* Sudden death without a previous time control. */
	if (!n && !tc)
	    return 1;

	m = n;
	p++;
	n = parse_clock_time(&p);

	if (n == -1)
	    return 1;

	if (tc >= MAX_TC) {
	    message(ERROR_STR, ANY_KEY_STR, "%s (%i)", _("Maximum number of time controls reached"), MAX_TC);
	    return 1;
	}

	clk->tc[tc][0] = m;
	clk->tc[tc++][1] = n;
	SKIP_SPACE(p);

	if (*p == '+')
	    goto move_incr;

	if (*p)
	    goto again;

	goto done;
    }

    if (plus)
	*incr = n;
    else
	clk->tc[clk->tcn][1] = (n <= clk->elapsed.tv_sec) ? clk->elapsed.tv_sec + n : n;

move_incr:
    if (*p) {
	if (*p++ == '+') {
	    if (!isdigit(*p))
		return 1;

	    n = parse_clock_time(&p);

	    if (n == -1 || *p)
		return 1;

	    clk->incr = n;

	    SKIP_SPACE(p);

	    if (*p)
		return 1;
	}
	else
	    return 1;
    }

done:
    return 0;
}

static int parse_which_clock(struct clock_s *clk, char *str)
{
    struct clock_s tmp;
    int incr = 0;

    memcpy(&tmp, clk, sizeof(struct clock_s));

    if (parse_clock_input(&tmp, str, &incr)) {
	cmessage(ERROR_STR, ANY_KEY_STR, _("Invalid clock specification"));
	return 1;
    }

    memcpy(clk, &tmp, sizeof(struct clock_s));
    clk->tc[clk->tcn][1] += incr;
    return 0;
}

void do_clock_input_finalize(WIN *win)
{
    struct userdata_s *d = gp->data;
    struct input_data_s *in = win->data;
    char *p = in->str;

    if (!in->str) {
	free(in);
	return;
    }

    SKIP_SPACE(p);

    if (tolower(*p) == 'w') {
	p++;

	if (parse_which_clock(&d->wclock, p))
	    goto done;
    }
    else if (tolower(*p) == 'b') {
	p++;

	if (parse_which_clock(&d->bclock, p))
	    goto done;
    }
    else {
	if (parse_which_clock(&d->wclock, p))
	    goto done;

	if (parse_which_clock(&d->bclock, p))
	    goto done;
    }

    if (!d->wclock.tc[0][1] && !d->bclock.tc[0][1])
	CLEAR_FLAG(d->flags, CF_CLOCK);
    else
	SET_FLAG(d->flags, CF_CLOCK);

done:
    free(in->str);
    free(in);
}

void do_engine_command_finalize(WIN *win)
{
    struct userdata_s *d = gp->data;
    struct input_data_s *in = win->data;
    int x;

    if (!in->str) {
	free(in);
	return;
    }

    if (!d->engine)
	goto done;

    x = d->engine->status;
    send_to_engine(gp, -1, "%s\n", in->str);
    d->engine->status = x;

done:
    free(in->str);
    free(in);
}

void do_board_details()
{
    config.details = (config.details) ? 0 : 1;
}

void do_toggle_strict_castling()
{
    int n;

    pgn_config_get(PGN_STRICT_CASTLING, &n);

    if (n == 0)
	pgn_config_set(PGN_STRICT_CASTLING, 1);
    else
	pgn_config_set(PGN_STRICT_CASTLING, 0);
}

void do_play_set_clock()
{
    struct input_data_s *in;

    in = Calloc(1, sizeof(struct input_data_s));
    in->efunc = do_clock_input_finalize;
    construct_input(_("Set Clock"), NULL, 1, 1,
		    _ ("Format: [W | B] [+]T[+I] | ++I | M/T [M/T [...] [SD/T]] [+I]\n" \
		       "T = time (hms), I = increment, M = moves per, SD = sudden death\ne.g., 30m or 4m+12s or 35/90m SD/30m"),
		    NULL, NULL, 0, in, INPUT_HIST_CLOCK, -1);
}

void do_play_toggle_human()
{
    struct userdata_s *d = gp->data;

    TOGGLE_FLAG(d->flags, CF_HUMAN);

    if (!TEST_FLAG(d->flags, CF_HUMAN) && pgn_history_total(gp->hp)) {
	if (init_chess_engine(gp))
	    return;
    }

    CLEAR_FLAG(d->flags, CF_ENGINE_LOOP);

    if (d->engine)
	d->engine->status = ENGINE_READY;
}

void do_play_toggle_engine()
{
    struct userdata_s *d = gp->data;

    TOGGLE_FLAG(d->flags, CF_ENGINE_LOOP);
    CLEAR_FLAG(d->flags, CF_HUMAN);

    if (d->engine && TEST_FLAG(d->flags, CF_ENGINE_LOOP)) {
        char *fen = pgn_game_to_fen (gp, d->b);

	pgn_board_update(gp, d->b,
		pgn_history_total(gp->hp));
	add_engine_command(gp, ENGINE_READY, "setboard %s\n", fen);
	free (fen);
    }
}

/*
 * This will send a command to the engine skipping the command queue.
 */
void do_play_send_command()
{
    struct userdata_s *d = gp->data;
    struct input_data_s *in;

    if (!d->engine || d->engine->status == ENGINE_OFFLINE) {
	if (init_chess_engine(gp))
	    return;
    }

    in = Calloc(1, sizeof(struct input_data_s));
    in->efunc = do_engine_command_finalize;
    construct_input(_("Engine Command"), NULL, 1, 1, NULL, NULL, NULL, 0, in, INPUT_HIST_ENGINE, -1);
}
/*
void do_play_switch_turn()
{
    struct userdata_s *d = gp->data;

    pgn_switch_side(gp);
    pgn_switch_turn(gp);

    if (!TEST_FLAG(d->flags, CF_HUMAN))
	add_engine_command(gp, -1,
		(gp->side == WHITE) ? "white\n" : "black\n");

    update_status_window(gp);
}
*/
void do_play_toggle_eh_mode()
{
    struct userdata_s *d = gp->data;

    if (!TEST_FLAG(d->flags, CF_HUMAN)) {
        if (!gp->hindex){
	    pgn_switch_side(gp, TRUE);
	    d->play_mode = (d->play_mode) ? PLAY_HE : PLAY_EH;
	    if (gp->side == BLACK)
	        update_status_notify(gp, _("Press 'g' to start the game"));

	    d->rotate = !d->rotate;
	}
	else
	    message(NULL, ANY_KEY_STR,
		    _("You may only switch sides at the start of the \n"
		      "game. Press ^K or ^N to begin a new game."));
    }
}

void do_play_undo()
{
    struct userdata_s *d = gp->data;

    if (!pgn_history_total(gp->hp))
	return;

    if (keycount) {
        if (gp->hindex - keycount < 0)
	    gp->hindex = 0;
	else {
	    if (d->go_move)
	        gp->hindex -= (keycount * 2) -1;
	    else
	        gp->hindex -= keycount * 2;
	}
    }
    else {
        if (gp->hindex - 2 < 0)
	    gp->hindex = 0;
	else {
	    if (d->go_move)
	        gp->hindex -= 1;
	    else
	        gp->hindex -= 2;
	}
    }

    pgn_history_free(gp->hp, gp->hindex);
    gp->hindex = pgn_history_total(gp->hp);
    pgn_board_update(gp, d->b, gp->hindex);

    if (d->engine && d->engine->status == ENGINE_READY) {
        char *fen = pgn_game_to_fen(gp, d->b);

        add_engine_command(gp, ENGINE_READY, "setboard %s\n", fen);
	free (fen);
	d->engine->status = ENGINE_READY;
    }

    update_history_window(gp);

    if (d->go_move) {
        pgn_switch_side(gp, FALSE);
	d->go_move--;
    }

    d->pm_undo = TRUE;
}

void do_play_toggle_pause()
{
    struct userdata_s *d = gp->data;

    if (!TEST_FLAG(d->flags, CF_HUMAN) && gp->turn !=
	    gp->side) {
	d->paused = -1;
	return;
    }

    d->paused = (d->paused) ? 0 : 1;
}

void do_play_go()
{
    struct userdata_s *d = gp->data;

    if (TEST_FLAG(d->flags, CF_HUMAN))
	return;

    if (fm_loaded_file && gp->side != gp->turn) {
        pgn_switch_side(gp, FALSE);
	add_engine_command(gp, ENGINE_THINKING, "black\n");
    }

    add_engine_command(gp, ENGINE_THINKING, "go\n");

    // Completa la función para que permita seguir jugando al usarla.
    // Complete the function to allow continue playing when using.
    if (gp->side == gp->turn)
        pgn_switch_side(gp, FALSE);

    d->go_move++;
}

void do_play_config_command()
{
    int x, w;

    if (config.keys) {
	for (x = 0; config.keys[x]; x++) {
	    if (config.keys[x]->c == input_c) {
		switch (config.keys[x]->type) {
		    case KEY_DEFAULT:
			add_engine_command(gp, -1, "%ls\n",
				config.keys[x]->str);
			break;
		    case KEY_SET:
			if (!keycount)
			    break;

			add_engine_command(gp, -1,
				"%ls %i\n", config.keys[x]->str, keycount);
			keycount = 0;
			break;
		    case KEY_REPEAT:
			if (!keycount)
			    break;

			for (w = 0; w < keycount; w++)
			    add_engine_command(gp, -1,
				    "%ls\n", config.keys[x]->str);
			keycount = 0;
			break;
		}
	    }
	}
    }

    update_status_notify(gp, NULL);
}

void do_play_cancel_selected()
{
    struct userdata_s *d = gp->data;

    d->sp.icon = d->sp.srow = d->sp.scol = 0;
    keycount = 0;
    pgn_reset_valid_moves(d->b);
    update_status_notify(gp, NULL);
}

void do_play_commit()
{
    struct userdata_s *d = gp->data;

    pushkey = keycount = 0;
    update_status_notify(gp, NULL);

    if (!TEST_FLAG(d->flags, CF_HUMAN) &&
	    (!d->engine || d->engine->status == ENGINE_THINKING))
	return;

    if (!d->sp.icon)
	return;

    d->sp.row = d->c_row;
    d->sp.col = d->c_col;

    if (d->rotate) {
        rotate_position(&d->sp.row, &d->sp.col);
	rotate_position(&d->sp.srow, &d->sp.scol);
    }

    move_to_engine(gp);

    // Completa la función para que permita seguir jugando cuando se carga un
    // archivo pgn (con juego no terminado) que inicie con turno del lado
    // negro.
    // Complete the function to allow continue playing when loading a file
    // pgn (with unfinished game) you start to turn black side.
    if (gp->side != gp->turn)
        pgn_switch_side(gp, FALSE);

    if (d->rotate && d->sp.icon)
        rotate_position(&d->sp.srow, &d->sp.scol);

    // Envia comando 'go' a Polyglot en el primer movimiento  debido a que
    // polyglot no envia el movimiento y cboard se queda esperando.
    // Send command 'go' to the first movement Polyglot  because cboard
    // waits to send polyglot movement and this does not make.
    if (config.fmpolyglot &&
	((gp->side == WHITE && !gp->hindex) || fm_loaded_file))
	add_engine_command(gp, ENGINE_THINKING, "go\n");

    d->go_move = 0;
    fm_loaded_file = FALSE;
    d->pm_undo = FALSE;
}

void do_play_select()
{
    struct userdata_s *d = gp->data;

    if (!TEST_FLAG(d->flags, CF_HUMAN) && (!d->engine ||
		d->engine->status == ENGINE_OFFLINE)) {
	if (init_chess_engine(gp))
	    return;
    }

    if (d->engine && d->engine->status == ENGINE_THINKING)
	return;

    if (d->sp.icon)
      do_play_cancel_selected ();

    if (d->rotate)
        rotate_position(&d->c_row, &d->c_col);

    d->sp.icon = d->b[RANKTOBOARD(d->c_row)][FILETOBOARD(d->c_col)].icon;

    if (pgn_piece_to_int(d->sp.icon) == OPEN_SQUARE) {
	d->sp.icon = 0;
	return;
    }

    if (((islower(d->sp.icon) && gp->turn != BLACK)
		|| (isupper(d->sp.icon) && gp->turn != WHITE))) {
        struct key_s **k;
        char *str = Malloc (512);

	for (k = play_keys; *k; k++) {
	  if ((*k)->f == do_play_toggle_eh_mode)
	        break;
	}

	snprintf (str, 512,  _("It is not your turn to move. You may switch playing sides by pressing \"%lc\"."),
		  *k ? (*k)->c : '?');
	message(NULL, ANY_KEY_STR, "%s", str);
	free (str);
	d->sp.icon = 0;
	return;
#if 0
	if (pgn_history_total(gp->hp)) {
	    message(NULL, ANY_KEY_STR, "%s", _("It is not your turn to move. You can switch sides "));
	    d->sp.icon = 0;
	    return;
	}
	else {
	    if (pgn_tag_find(gp->tag, "FEN") != E_PGN_ERR)
		return;

	    add_engine_command(gp, ENGINE_READY, "black\n");
	    pgn_switch_turn(gp);

	    if (gp->side != BLACK)
		pgn_switch_side(gp);
	}
#endif
    }

    d->sp.srow = d->c_row;
    d->sp.scol = d->c_col;

    if (config.validmoves)
	pgn_find_valid_moves(gp, d->b, d->sp.scol, d->sp.srow);

    if (d->rotate) {
        rotate_position(&d->c_row, &d->c_col);
	rotate_position(&d->sp.srow, &d->sp.scol);
    }

    CLEAR_FLAG(d->flags, CF_NEW);
    start_clock(gp);
}

static wchar_t *build_help(struct key_s **keys)
{
    int i, nlen = 1, len, t, n;
    wchar_t *buf = NULL, *wc = NULL;
    wchar_t *p;

    if (!keys)
	return NULL;

    for (i = len = t = 0; keys[i]; i++) {
	if (!keys[i]->d)
	    continue;

	if (keys[i]->key) {
	    if (wcslen(keys[i]->key) > nlen) {
		nlen = wcslen(keys[i]->key);
		t += nlen;
	    }
	    else
		t++;
	}
	else
	    t++;

	if (keys[i]->d) {
	    if (wcslen(keys[i]->d) > len)
		len = wcslen(keys[i]->d);
	}

	t += len;
	t += keys[i]->r;
    }

    t += 4 + i + 1;
    buf = Malloc((t+1)*sizeof(wchar_t));
    p = buf;

    for (i = 0; keys[i]; i++) {
	if (!keys[i]->d)
	    continue;

	if (keys[i]->key)
	    n = wcslen(keys[i]->key);
	else
	    n = 1;

	while (n++ <= nlen)
	    *p++ = ' ';

	*p = 0;

	if (keys[i]->key) {
	    wcsncat(buf, keys[i]->key, t-1);
	    p = buf + wcslen(buf);
	}
	else
	    *p++ = keys[i]->c;

	*p++ = ' ';
	*p++ = '-';
	*p++ = ' ';
	*p = 0;

	if (keys[i]->d)
	    wcsncat(buf, keys[i]->d, t-1);

	if (keys[i]->r) {
	    wc = str_to_wchar ("*");
	    wcsncat(buf, wc, t-1);
	    free (wc);
	}

	wc = str_to_wchar ("\n");
	wcscat(buf, wc);
	free (wc);
	p = buf + wcslen(buf);
    }

    return buf;
}

void do_global_help ()
{
    wchar_t *buf = build_help(global_keys);

    construct_message(_("Global Game Keys (* = can take a repeat count)"),
		      ANY_KEY_SCROLL_STR, 0, 0, NULL, NULL, buf, do_more_help,
		      0, 1, "%ls", buf);
}

void do_main_help(WIN *win)
{
    switch (win->c) {
	case 'p':
	    do_play_help ();
	    break;
	case 'h':
	    do_history_help ();
	    break;
	case 'e':
	    do_edit_help ();
	    break;
	case 'g':
	    do_global_help ();
	    break;
	default:
	    break;
    }
}

static void do_more_help(WIN *win)
{
    if (win->c == KEY_F(1) || win->c == CTRL_KEY('g'))
      construct_message(_("Command Key Index"),
			_ ("p/h/e/g or any other key to quit"), 0, 0,
			NULL, NULL, NULL, do_main_help, 0, 0, "%s",
			_ (
			   "p - play mode keys\n"
			   "h - history mode keys\n"
			   "e - board edit mode keys\n"
			   "g - global game keys"
			   ));
}

void do_play_help()
{
    wchar_t *buf = build_help(play_keys);

    construct_message(_("Play Mode Keys (* = can take a repeat count)"),
		      ANY_KEY_SCROLL_STR, 0, 0, NULL, NULL,
		      buf, do_more_help, 0, 1, "%ls", buf);
}

void do_play_history_mode()
{
    struct userdata_s *d = gp->data;

    if (!pgn_history_total(gp->hp) ||
	    (d->engine && d->engine->status == ENGINE_THINKING))
	return;

    d->mode = MODE_HISTORY;
    pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
}

void do_play_edit_mode()
{
    struct userdata_s *d = gp->data;

    if (pgn_history_total(gp->hp))
	return;

    pgn_board_init_fen(gp, d->b, NULL);
    config.details++;
    d->mode = MODE_EDIT;
}

void do_edit_insert_finalize(WIN *win)
{
    struct userdata_s *d = win->data;

    if (pgn_piece_to_int(win->c) == -1)
	return;

    d->b[RANKTOBOARD(d->c_row)][FILETOBOARD(d->c_col)].icon = win->c;
}

void do_edit_select()
{
    struct userdata_s *d = gp->data;

    if (d->sp.icon)
	return;

    d->sp.icon = d->b[RANKTOBOARD(d->c_row)][FILETOBOARD(d->c_col)].icon;

    if (pgn_piece_to_int(d->sp.icon) == OPEN_SQUARE) {
	d->sp.icon = 0;
	return;
    }

    d->sp.srow = d->c_row;
    d->sp.scol = d->c_col;
}

void do_edit_commit()
{
    int p;
    struct userdata_s *d = gp->data;

    pushkey = keycount = 0;
    update_status_notify(gp, NULL);

    if (!d->sp.icon)
	return;

    d->sp.row = d->c_row;
    d->sp.col = d->c_col;
    p = d->b[RANKTOBOARD(d->sp.srow)][FILETOBOARD(d->sp.scol)].icon;
    d->b[RANKTOBOARD(d->sp.row)][FILETOBOARD(d->sp.col)].icon = p;
    d->b[RANKTOBOARD(d->sp.srow)][FILETOBOARD(d->sp.scol)].icon =
	pgn_int_to_piece(gp->turn, OPEN_SQUARE);
    d->sp.icon = d->sp.srow = d->sp.scol = 0;
}

void do_edit_delete()
{
    struct userdata_s *d = gp->data;

    if (d->sp.icon)
	d->b[RANKTOBOARD(d->sp.srow)][FILETOBOARD(d->sp.scol)].icon =
	    pgn_int_to_piece(gp->turn, OPEN_SQUARE);
    else
	d->b[RANKTOBOARD(d->c_row)][FILETOBOARD(d->c_col)].icon =
	    pgn_int_to_piece(gp->turn, OPEN_SQUARE);

    d->sp.icon = d->sp.srow = d->sp.scol = 0;
}

void do_edit_cancel_selected()
{
    struct userdata_s *d = gp->data;

    d->sp.icon = d->sp.srow = d->sp.scol = 0;
    keycount = 0;
    update_status_notify(gp, NULL);
}

void do_edit_switch_turn()
{
    pgn_switch_turn(gp);
}

void do_edit_toggle_castle()
{
    struct userdata_s *d = gp->data;

    castling_state(gp, d->b, RANKTOBOARD(d->c_row),
	    FILETOBOARD(d->c_col),
	    d->b[RANKTOBOARD(d->c_row)][FILETOBOARD(d->c_col)].icon, 1);
}

void do_edit_insert()
{
    struct userdata_s *d = gp->data;

    construct_message(_("Insert Piece"), _("P=pawn, R=rook, N=knight, B=bishop, "), 0, 0, NULL, NULL,
	    d->b, do_edit_insert_finalize, 0, 0, "%s", _("Type the piece letter to insert. Lowercase "));
}

void do_edit_enpassant()
{
    struct userdata_s *d = gp->data;

    if (d->c_row == 6 || d->c_row == 3) {
	pgn_reset_enpassant(d->b);
	d->b[RANKTOBOARD(d->c_row)][FILETOBOARD(d->c_col)].enpassant = 1;
    }
}

void do_edit_help()
{
    wchar_t *buf = build_help(edit_keys);

    construct_message(_("Edit Mode Keys (* = can take a repeat count)"),
		      ANY_KEY_SCROLL_STR, 0, 0, NULL, NULL, buf, do_more_help,
		      0, 1, "%ls", buf);
}

void do_edit_exit()
{
    struct userdata_s *d = gp->data;
    char *fen = pgn_game_to_fen(gp, d->b);

    config.details--;
    pgn_tag_add(&gp->tag, "FEN", fen);
    free (fen);
    pgn_tag_add(&gp->tag, "SetUp", "1");
    pgn_tag_sort(gp->tag);
    pgn_board_update(gp, d->b, gp->hindex);
    d->mode = MODE_PLAY;
}

void really_do_annotate_finalize(struct input_data_s *in,
	struct userdata_s *d)
{
    HISTORY *h = in->data;
    int len;

    if (!in->str) {
	if (h->comment) {
	    free(h->comment);
	    h->comment = NULL;
	}
    }
    else {
	len = strlen(in->str);
	h->comment = Realloc(h->comment, len+1);
	strncpy(h->comment, in->str, len);
	h->comment[len] = 0;
    }

    free(in->str);
    free(in);
    SET_FLAG(d->flags, CF_MODIFIED);
}

void do_annotate_finalize(WIN *win)
{
    struct userdata_s *d = gp->data;
    struct input_data_s *in = win->data;

    really_do_annotate_finalize(in, d);
}

void do_find_move_exp_finalize(int init, int which)
{
    int n;
    struct userdata_s *d = gp->data;
    static int firstrun;
    static regex_t r;
    int ret;
    char errbuf[255];

    if (init || !firstrun) {
	if (!firstrun)
	    regfree(&r);

	if ((ret = regcomp(&r, moveexp, REG_EXTENDED|REG_NOSUB)) != 0) {
	    regerror(ret, &r, errbuf, sizeof(errbuf));
	    cmessage(_("Error Compiling Regular Expression"), ANY_KEY_STR, "%s", errbuf);
	    return;
	}

	firstrun = 1;
    }

    if ((n = find_move_exp(gp, r,
		    (which == -1) ? 0 : 1, (keycount) ? keycount : 1)) == -1)
	return;

    gp->hindex = n;
    pgn_board_update(gp, d->b, gp->hindex);
}

void do_find_move_exp(WIN *win)
{
    struct input_data_s *in = win->data;
    int *n = in->data;
    int which = *n;

    if (in->str) {
	strncpy(moveexp, in->str, sizeof(moveexp)-1);
	moveexp[sizeof(moveexp)-1] = 0;
	do_find_move_exp_finalize(1, which);
	free(in->str);
    }

    free(in->data);
    free(in);
}

void do_move_jump_finalize(int n)
{
    struct userdata_s *d = gp->data;

    if (n < 0 || n > (pgn_history_total(gp->hp) / 2))
	return;

    keycount = 0;
    update_status_notify(gp, NULL);
    gp->hindex = (n) ? n * 2 - 1 : n * 2;
    pgn_board_update(gp, d->b, gp->hindex);
}

void do_move_jump(WIN *win)
{
    struct input_data_s *in = win->data;

    if (!in->str || !isinteger(in->str)) {
	if (in->str)
	    free(in->str);

	free(in);
	return;
    }

    do_move_jump_finalize(atoi(in->str));
    free(in->str);
    free(in);
}

struct history_menu_s {
    char *line;
    int hindex;
    int ravlevel;
    int move;
    int indent;
};

void free_history_menu_data(struct history_menu_s **h)
{
    int i;

    if (!h)
	return;

    for (i = 0; h[i]; i++) {
	free(h[i]->line);
	free(h[i]);
    }

    free(h);
}

void get_history_data(HISTORY **hp, struct history_menu_s ***menu, int m,
	int turn)
{
    int i, n = 0;
    int t = pgn_history_total(hp);
    char buf[MAX_SAN_MOVE_LEN + 4];
    static int depth;
    struct history_menu_s **hmenu = *menu;

    if (hmenu)
	for (n = 0; hmenu[n]; n++);
    else
	depth = 0;

    for (i = 0; i < t; i++) {
	hmenu = Realloc(hmenu, (n + 2) * sizeof(struct history_menu_s *));
	hmenu[n] = Malloc(sizeof(struct history_menu_s));
	snprintf(buf, sizeof(buf), "%c%s%s", (turn == WHITE) ? 'W' : 'B',
		hp[i]->move, (hp[i]->comment || hp[i]->nag[0]) ? " !" : "");
	hmenu[n]->line = strdup(buf);
	hmenu[n]->hindex = i;
	hmenu[n]->indent = 0;
	hmenu[n]->ravlevel = depth;
	hmenu[n]->move = (n && depth > hmenu[n-1]->ravlevel) ? m++ : m;
	n++;
	hmenu[n] = NULL;

#if 0
	if (hp[i]->rav) {
	    depth++;
	    get_history_data(hp[i]->rav, &hmenu, m, turn);
	    for (n = 0; hmenu[n]; n++);
	    depth--;

	    if (depth)
		m--;
	}
#endif

	turn = (turn == WHITE) ? BLACK : WHITE;
    }

    *menu = hmenu;
}

void history_draw_update(struct menu_input_s *m)
{
    GAME g = m->data;
    struct userdata_s *d = g->data;

    g->hindex = m->selected + 1;
    update_cursor(g, m->selected);
    pgn_board_update(g, d->b, m->selected + 1);
}

struct menu_item_s **get_history_items(WIN *win)
{
    struct menu_input_s *m = win->data;
    GAME g = m->data;
    struct userdata_s *d = g->data;
    struct history_menu_s **hm = d->data;
    struct menu_item_s **items = m->items;
    int i;

    if (!hm) {
	get_history_data(g->history, &hm, 0,
		TEST_FLAG(g->flags, GF_BLACK_OPENING));
	m->selected = g->hindex - 1;

	if (m->selected < 0)
	    m->selected = 0;

	m->draw_exit_func = history_draw_update;
    }

    d->data = hm;

    if (items) {
	for (i = 0; items[i]; i++)
	    free(items[i]);

	free(items);
	items = NULL;
    }

    for (i = 0; hm[i]; i++) {
	items = Realloc(items, (i+2) * sizeof(struct menu_item_s *));
	items[i] = Malloc(sizeof(struct menu_item_s));
	items[i]->name = hm[i]->line;
	items[i]->value = NULL;
	items[i]->selected = 0;
    }

    if (items)
	items[i] = NULL;

    m->nofree = 1;
    m->items = items;
    return items;
}

void history_menu_quit(struct menu_input_s *m)
{
    pushkey = -1;
}

void history_menu_exit(WIN *win)
{
    GAME g = win->data;
    struct userdata_s *d = g->data;
    struct history_menu_s **hm = d->data;
    int i;

    if (!hm)
	return;

    for (i = 0; hm[i]; i++) {
	free(hm[i]->line);
	free(hm[i]);
    }

    free(hm);
    d->data = NULL;
}

// FIXME RAV
void history_menu_next(struct menu_input_s *m)
{
    GAME g = m->data;
    struct userdata_s *d = g->data;
    struct history_menu_s **hm = d->data;
    int n, t;

    for (t = 0; hm[t]; t++);

    if (m->selected + 1 == t)
	n = 0;
    else
	n = hm[m->selected + 1]->hindex;

    n++;
    g->hindex = n;
}

// FIXME RAV
void history_menu_prev(struct menu_input_s *m)
{
    GAME g = m->data;
    struct userdata_s *d = g->data;
    struct history_menu_s **hm = d->data;
    int n, t;

    for (t = 0; hm[t]; t++);

    if (m->selected - 1 < 0)
	n = t - 1;
    else
	n = hm[m->selected - 1]->hindex;

    n++;
    g->hindex = n;
}

void history_menu_help(struct menu_input_s *m)
{
    message(_("History Menu Help"), ANY_KEY_STR, "%s",
	    _ (
	       "    UP/DOWN - previous/next menu item\n"
	       "   HOME/END - first/last menu item\n"
	       "  PGDN/PGUP - next/previous page\n"
	       "  a-zA-Z0-9 - jump to item\n"
	       "     CTRL-a - annotate the selected move\n"
	       "      ENTER - view annotation\n"
	       "     CTRL-d - toggle board details\n"
	       "   ESCAPE/M - return to move history"
	       ));
}

void do_annotate_move(HISTORY *hp)
{
    char buf[COLS - 4];
    struct input_data_s *in;

    snprintf(buf, sizeof(buf), "%s \"%s\"", _("Editing Annotation for"), hp->move);
    in = Calloc(1, sizeof(struct input_data_s));
    in->data = hp;
    in->efunc = do_annotate_finalize;
    construct_input(buf, hp->comment, MAX_PGN_LINE_LEN / INPUT_WIDTH, 0,
	    _("Type CTRL-t to edit NAG"), edit_nag, NULL, CTRL_KEY('T'), in, -1, -1);
}

void history_menu_view_annotation(struct menu_input_s *m)
{
    GAME g = m->data;

    // FIXME RAV
    view_annotation(g->history[m->selected]);
}

void history_menu_annotate_finalize(WIN *win)
{
    struct input_data_s *in = win->data;
    GAME g = in->moredata;
    struct userdata_s *d = g->data;
    struct history_menu_s **hm = d->data;

    really_do_annotate_finalize(in, d);
    free_history_menu_data(hm);
    hm = NULL;
    get_history_data(g->history, &hm, 0, TEST_FLAG(g->flags, GF_BLACK_OPENING));
    d->data = hm;
    pushkey = REFRESH_MENU;
}

void history_menu_annotate(struct menu_input_s *m)
{
    GAME g = m->data;
    char buf[COLS - 4];
    struct input_data_s *in;
    HISTORY *hp = g->history[m->selected]; // FIXME RAV

    snprintf(buf, sizeof(buf), "%s \"%s\"", _("Editing Annotation for"), hp->move);
    in = Calloc(1, sizeof(struct input_data_s));
    in->data = hp;
    in->moredata = m->data;
    in->efunc = history_menu_annotate_finalize;
    construct_input(buf, hp->comment, MAX_PGN_LINE_LEN / INPUT_WIDTH, 0,
	    _("Type CTRL-t to edit NAG"), edit_nag, NULL, CTRL_KEY('T'), in, -1, -1);
}

void history_menu_details(struct menu_input_s *m)
{
    do_board_details();
}

// FIXME RAV
void history_menu_print(WIN *win)
{
    struct menu_input_s *m = win->data;
    GAME g = m->data;
    struct userdata_s *d = g->data;
    struct history_menu_s **hm = d->data;
    struct history_menu_s *h = hm[m->top];
    int i;
    char *p = m->item->name;
    int line = m->print_line - 2;
/*
 * Solaris 5.9 doesn't have wattr_get() or any function that requires an
 * attr_t data type.
 */
    attr_t attrs;
    short pair;
    int total;

    for (total = 0; hm[total]; total++);
    wattr_get(win->w, &attrs, &pair, NULL);
    wattroff(win->w, COLOR_PAIR(pair));
    mvwaddch(win->w, m->print_line, 1,
	    *p == 'W' ? *p | mix_cp(CP_BOARD_WHITE, CP_HISTORY_WINDOW, ATTRS(CP_BOARD_WHITE), A_FG_B_BG) : *p | mix_cp(CP_BOARD_BLACK, CP_HISTORY_WINDOW, ATTRS(CP_BOARD_BLACK), A_FG_B_BG));
    p++;

    if (h->hindex == 0 && line == 0)
	waddch(win->w, ACS_ULCORNER | CP_HISTORY_MENU_LG);
    else if ((!hm[h->hindex + (win->rows - 5) + 1] && line == win->rows - 5) ||
	    (m->top + line == total - 1))
	waddch(win->w, ACS_LLCORNER | CP_HISTORY_MENU_LG);
    else if (hm[m->top + 1]->ravlevel != h->ravlevel || !h->ravlevel)
	waddch(win->w, ACS_LTEE | CP_HISTORY_MENU_LG);
    else
	waddch(win->w, ACS_VLINE | CP_HISTORY_MENU_LG);

    wattron(win->w, COLOR_PAIR(pair) | attrs);

    for (i = 2; *p; p++, i++)
	waddch(win->w, (*p == '!') ? *p | A_BOLD : *p);

    while (i++ < win->cols - 2)
	waddch(win->w, ' ');
}

void history_menu(GAME g)
{
    struct menu_key_s **keys = NULL;

    add_menu_key(&keys, KEY_ESCAPE, history_menu_quit);
    add_menu_key(&keys, 'M', history_menu_quit);
    add_menu_key(&keys, KEY_UP, history_menu_prev);
    add_menu_key(&keys, KEY_DOWN, history_menu_next);
    add_menu_key(&keys, KEY_F(1), history_menu_help);
    add_menu_key(&keys, CTRL_KEY('a'), history_menu_annotate);
    add_menu_key(&keys, CTRL_KEY('d'), history_menu_details);
    add_menu_key(&keys, '\n', history_menu_view_annotation);
    construct_menu(MEGA_BOARD ? LINES - HISTORY_HEIGHT_MB : LINES,
			TAG_WIDTH, 0, config.boardleft ? BOARD_WIDTH : 0,
			_("Move History Tree"), 1, get_history_items, keys, g,
			history_menu_print, history_menu_exit);
}

void do_history_menu()
{
    history_menu(gp);
}

void do_history_half_move_toggle()
{
    movestep = (movestep == 1) ? 2 : 1;
    update_history_window(gp);
}

void do_history_rotate_board()
{
    struct userdata_s *d = gp->data;
    d->rotate = !d->rotate;
}

void do_history_jump_next()
{
    struct userdata_s *d = gp->data;

    pgn_history_next(gp, d->b, (keycount > 0) ?
	    config.jumpcount * keycount * movestep :
	    config.jumpcount * movestep);
}

void do_history_jump_prev()
{
    struct userdata_s *d = gp->data;

    pgn_history_prev(gp, d->b, (keycount) ?
	    config.jumpcount * keycount * movestep :
	    config.jumpcount * movestep);
}

void do_history_prev()
{
    struct userdata_s *d = gp->data;

    pgn_history_prev(gp, d->b,
	    (keycount) ? keycount * movestep : movestep);
}

void do_history_next()
{
    struct userdata_s *d = gp->data;

    pgn_history_next(gp, d->b, (keycount) ?
	    keycount * movestep : movestep);
}

void do_history_mode_finalize(struct userdata_s *d)
{
    pushkey = 0;
    d->mode = MODE_PLAY;
}

void do_history_mode_confirm(WIN *win)
{
    struct userdata_s *d = gp->data;
    wchar_t str[] = { win->c, 0 };

    if (!wcscmp (str, resume_wchar)) {
        pgn_history_free(gp->hp, gp->hindex);
	pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
    }
#if 0
	case 'C':
	case 'c':
	    if (pgn_history_rav_new(gp, d->b,
			gp->hindex) != E_PGN_OK)
		return;

	    break;
#endif
     else
         return;

    if (!TEST_FLAG(d->flags, CF_HUMAN)) {
        char *fen =  pgn_game_to_fen(gp, d->b);

	add_engine_command(gp, ENGINE_READY, "setboard %s\n", fen);
	free (fen);
    }

    do_history_mode_finalize(d);
}

void do_history_toggle()
{
    struct userdata_s *d = gp->data;

    // FIXME Resuming from previous history could append to a RAV.
    if (gp->hindex != pgn_history_total(gp->hp)) {
	if (!pushkey)
	    construct_message(NULL, _ ("What would you like to do?"), 0, 1,
			      NULL, NULL, NULL, do_history_mode_confirm, 0, 0,
			      _("The current move is not the final move of this round. Press \"%ls\" to resume a game from the current move and discard future moves or any other key to cancel."),
			      resume_wchar);
	return;
    }
    else {
	if (TEST_FLAG(gp->flags, GF_GAMEOVER))
	    return;
    }

    if (gp->side != gp->turn) {
        d->play_mode = PLAY_EH;
    }
    else {
        d->play_mode = PLAY_HE;
	d->rotate = FALSE;
    }

    do_history_mode_finalize(d);
}

void do_history_annotate()
{
    int n = gp->hindex;

    if (n && gp->hp[n - 1]->move)
	n--;
    else
	return;

    do_annotate_move(gp->hp[n]);
}

void do_history_help()
{
    wchar_t *buf = build_help(history_keys);

    construct_message(_("History Mode Keys (* = can take a repeat count)"),
		      ANY_KEY_SCROLL_STR, 0, 0, NULL, NULL,
		      buf, do_more_help, 0, 1, "%ls", buf);
}

void do_history_find(int which)
{
    struct input_data_s *in;
    int *p;

    if (pgn_history_total(gp->hp) < 2)
	return;

    in = Calloc(1, sizeof(struct input_data_s));
    p = Malloc(sizeof(int));
    *p = which;
    in->data = p;
    in->efunc = do_find_move_exp;

    if (!*moveexp || which == 0) {
	construct_input(_("Find Move Text Expression"), NULL, 1, 0, NULL, NULL, NULL,
		0, in, INPUT_HIST_MOVE_EXP, -1);
	return;
    }

    free(p);
    free(in);
    do_find_move_exp_finalize(0, which);
}

void do_history_find_new()
{
    do_history_find(0);
}

void do_history_find_prev()
{
    do_history_find(-1);
}

void do_history_find_next()
{
    do_history_find(1);
}

void do_history_rav(int which)
{
    struct userdata_s *d = gp->data;

    rav_next_prev(gp, d->b, which);
}

void do_history_rav_next()
{
    do_history_rav(1);
}

void do_history_rav_prev()
{
    do_history_rav(0);
}

void do_history_jump()
{
    struct input_data_s *in;

    if (pgn_history_total(gp->hp) < 2)
	return;

    if (!keycount) {
	in = Calloc(1, sizeof(struct input_data_s));
	in->efunc = do_move_jump;

	construct_input(_("Jump to Move Number"), NULL, 1, 1, NULL,
		NULL, NULL, 0, in, -1, 0);
	return;
    }

    do_move_jump_finalize(keycount);
}

static void free_userdata_once(GAME g)
{
    struct userdata_s *d = g->data;

    if (!d)
	return;

    if (d->engine) {
	stop_engine(g);

	if (d->engine->enginebuf) {
	    int n;

	    for (n = 0; d->engine->enginebuf[n]; n++)
		free(d->engine->enginebuf[n]);

	    free(d->engine->enginebuf);
	}

	if (d->engine->queue) {
	    struct queue_s **q;

	    for (q = d->engine->queue; *q; q++)
		free(*q);

	    free(d->engine->queue);
	}

	free(d->engine);
    }

#ifdef WITH_LIBPERL
    if (d->perlfen)
	free(d->perlfen);

    if (d->oldfen)
	free(d->oldfen);
#endif

    free(d);
    g->data = NULL;
}

static void free_userdata()
{
    int i;

    for (i = 0; i < gtotal; i++) {
	free_userdata_once(game[i]);
	game[i]->data = NULL;
    }
}

void update_loading_window(int n)
{
    char buf[16];

    if (!loadingw) {
	loadingw = newwin(3, COLS / 2, CALCPOSY(3), CALCPOSX(COLS / 2));
	loadingp = new_panel(loadingw);
	wbkgd(loadingw, CP_MESSAGE_WINDOW);
    }

    wmove(loadingw, 0, 0);
    wclrtobot(loadingw);
    wattron(loadingw, CP_MESSAGE_BORDER);
    box(loadingw, ACS_VLINE, ACS_HLINE);
    wattroff(loadingw, CP_MESSAGE_BORDER);
    mvwprintw(loadingw, 1, CENTER_INT((COLS / 2), 11 +
				      strlen(itoa(gtotal, buf))),
	      _("Loading... %i%% (%i games)"), n, gtotal);
    update_panels();
    doupdate();
}

static void init_userdata_once(GAME g, int n)
{
    struct userdata_s *d = NULL;

    d = Calloc(1, sizeof(struct userdata_s));
    d->n = n;
    d->c_row = 2, d->c_col = 5;
    SET_FLAG(d->flags, CF_NEW);
    g->data = d;

    if (pgn_board_init_fen(g, d->b, NULL) != E_PGN_OK)
	pgn_board_init(d->b);
}

void init_userdata()
{
    int i;

    for (i = 0; i < gtotal; i++)
	init_userdata_once(game[i], i);
}

void fix_marks(int *start, int *end)
{
    int i;

    *start = (*start < 0) ? 0 : *start;
    *end = (*end < 0) ? 0 : *end;

    if (*start > *end) {
	i = *start;
	*start = *end;
        *end = i + 1;
    }

    *end = (*end > gtotal) ? gtotal : *end;
}

void do_new_game_finalize(GAME g)
{
    struct userdata_s *d = g->data;

    d->mode = MODE_PLAY;
    update_status_notify(g, NULL);
    d->rotate = FALSE;
    d->go_move = 0;
}

void do_new_game_from_scratch(WIN *win)
{
    wchar_t str[] = {  win->c, 0 };

    if (wcscmp (str, yes_wchar))
        return;

    stop_clock();
    free_userdata();
    pgn_parse(NULL);
    gp = game[gindex];
    add_custom_tags(&gp->tag);
    init_userdata();
    loadfile[0] = 0;
    do_new_game_finalize(gp);
}

void do_new_game()
{
    pgn_new_game();
    gp = game[gindex];
    add_custom_tags(&gp->tag);
    init_userdata_once(gp, gindex);
    do_new_game_finalize(gp);
}

void do_game_delete_finalize(int n)
{
    struct userdata_s *d;

    delete_game((!n) ? gindex : -1);
    d = gp->data;
    if (d->mode != MODE_EDIT)
	pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
}

void do_game_delete_confirm(WIN *win)
{
    int *n;
    wchar_t str[] = { win->c, 0 };

    if (wcscmp (str, yes_wchar)) {
	free(win->data);
	return;
    }

    n = (int *)win->data;
    do_game_delete_finalize(*n);
    free(win->data);
}

void do_game_delete()
{
    char *tmp = NULL;
    int i, n;
    struct userdata_s *d;
    int *p;

    if (gtotal < 2) {
	cmessage(NULL, ANY_KEY_STR, "%s", _("Cannot delete last game."));
	return;
    }

    tmp = NULL;

    for (i = n = 0; i < gtotal; i++) {
	d = game[i]->data;

	if (TEST_FLAG(d->flags, CF_DELETE))
	    n++;
    }

    if (!n)
	tmp = _("Delete the current game?");
    else {
	if (n == gtotal) {
	    cmessage(NULL, ANY_KEY_STR, "%s", _("Cannot delete last game."));
	    return;
	}

	tmp = _("Delete all games marked for deletion?");
    }

    if (config.deleteprompt) {
	p = Malloc(sizeof(int));
	*p = n;
	construct_message(NULL, _("[ Yes or No ]"), 1, 1, NULL, NULL, p,
		do_game_delete_confirm, 0, 0, tmp);
	return;
    }

    do_game_delete_finalize(n);
}

void do_find_game_exp_finalize(int which)
{
    struct userdata_s *d = gp->data;
    int n;

    if ((n = find_game_exp(gameexp, (which == -1) ? 0 : 1,
		    (keycount) ? keycount : 1)) == -1) {
	update_status_notify(gp, "%s", _("No matches found"));
	return;
    }

    gindex = n;
    d = gp->data;

    if (pgn_history_total(gp->hp))
	d->mode = MODE_HISTORY;

    pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
}

void do_find_game_exp(WIN *win)
{
    struct input_data_s *in = win->data;
    int *n = in->data;
    int c = *n;

    if (in->str) {
	strncpy(gameexp, in->str, sizeof(gameexp));
	gameexp[sizeof(gameexp)-1] = 0;

	if (c == '?')
	    c = '}';

	do_find_game_exp_finalize(c);
	free(in->str);
    }

    free(in->data);
    free(in);
}

void do_game_jump_finalize(int n)
{
    struct userdata_s *d;

    if (--n > gtotal - 1 || n < 0)
	return;

    gindex = n;
    gp = game[gindex];
    d = gp->data;
    pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
    update_status_notify(gp, NULL);
}

void do_game_jump(WIN *win)
{
    struct input_data_s *in = win->data;

    if (!in->str || !isinteger(in->str)) {
	if (in->str)
	    free(in->str);

	free(in);
	return;
    }

    do_game_jump_finalize(atoi(in->str));
    free(in->str);
    free(in);
}

void do_load_file(WIN *win)
{
    struct input_data_s *in = win->data;
    char *tmp = in->str;
    struct userdata_s *d;
    PGN_FILE *pgn = NULL;
    int n;

    if (!in->str) {
	free(in);
	return;
    }

    if ((tmp = pathfix(tmp)) == NULL)
	goto done;

    n = pgn_open(tmp, "r", &pgn);

    if (n == E_PGN_ERR) {
	cmessage(ERROR_STR, ANY_KEY_STR, "%s\n%s", tmp, strerror(errno));
	goto done;
    }
    else if (n == E_PGN_INVALID) {
	cmessage(ERROR_STR, ANY_KEY_STR, "%s\n%s", tmp, _("Not a regular file"));
	goto done;
    }

    free_userdata();

    if (pgn_parse(pgn) == E_PGN_ERR) {
	del_panel(loadingp);
	delwin(loadingw);
	loadingw = NULL;
	loadingp = NULL;
	init_userdata();
	goto done;
    }

    del_panel(loadingp);
    delwin(loadingw);
    loadingw = NULL;
    loadingp = NULL;
    init_userdata();
    strncpy(loadfile, tmp, sizeof(loadfile));
    loadfile[sizeof(loadfile)-1] = 0;
    gp = game[gindex];
    d = gp->data;

    if (pgn_history_total(gp->hp))
	d->mode = MODE_HISTORY;

    pgn_board_update(gp, d->b, pgn_history_total(gp->hp));

    fm_loaded_file = TRUE;
	d->rotate = FALSE;

done:
    pgn_close(pgn);

    if (in->str)
	free(in->str);

    free(in);
}

void do_game_save(WIN *win)
{
    struct input_data_s *in = win->data;
    int *x = in->data;
    int n = *x;
    char *tmp = in->str;
    char tfile[FILENAME_MAX];
    char *p;
    int i;
    struct userdata_s *d;

    if (!tmp || (tmp = pathfix(tmp)) == NULL)
	goto done;

    if (pgn_is_compressed(tmp) == E_PGN_ERR) {
	p = tmp + strlen(tmp) - 1;

	if (*p != 'n' || *(p-1) != 'g' || *(p-2) != 'p' ||
		*(p-3) != '.') {
	    snprintf(tfile, sizeof(tfile), "%s.pgn", tmp);
	    tmp = tfile;
	}
    }

    /*
     * When in edit mode, update the FEN tag.
     */
    if (n == -1) {
	for (i = 0; i < gtotal; i++) {
	    d = game[i]->data;

	    if (d->mode == MODE_EDIT) {
	        char *fen = pgn_game_to_fen(game[i], d->b);

		pgn_tag_add(&game[i]->tag, "FEN", fen);
		free (fen);
	    }
	}
    }
    else {
	d = game[n]->data;

	if (d->mode == MODE_EDIT) {
	    char *fen = pgn_game_to_fen(game[n], d->b);

	    pgn_tag_add(&game[n]->tag, "FEN", fen);
	    free (fen);
	}
    }

    save_pgn(tmp, n);

done:
    if (in->str)
	free(in->str);

    free(in->data);
    free(in);
}

void do_get_game_save_input(int n)
{
    struct input_data_s *in = Calloc(1, sizeof(struct input_data_s));
    int *p = Malloc(sizeof(int));

    in->efunc = do_game_save;
    *p = n;
    in->data = p;

    construct_input(_("Save Game Filename"), loadfile, 1, 1, _("Type TAB for file browser"),
	file_browser, NULL, '\t', in, INPUT_HIST_FILE, -1);
}

void do_game_save_multi_confirm(WIN *win)
{
    int i;
    wchar_t str[] = { win->c, 0 };

    if (!wcscmp (str, current_wchar))
	i = gindex;
    else if (!wcscmp (str, all_wchar))
	i = -1;
    else {
	update_status_notify(gp, "%s", _("Save game aborted."));
	return;
    }

    do_get_game_save_input(i);
}

void do_global_about()
{
    cmessage(_("ABOUT"), ANY_KEY_STR,
	     _("%s\nUsing %s with %i colors and %i color pairs\n%s"),
	     PACKAGE_STRING, curses_version(), COLORS, COLOR_PAIRS,
	     COPYRIGHT);
}

void global_game_next_prev(int which)
{
    struct userdata_s *d;

    game_next_prev(gp, (which == 1) ? 1 : 0,
	    (keycount) ? keycount : 1);
    d = gp->data;

    if (delete_count) {
	if (which == 1) {
	    markend = markstart + delete_count;
	    delete_count = 0;
	}
	else {
	    markend = markstart - delete_count + 1;
	    delete_count = -1; // to fix gindex in the other direction
	}

	fix_marks(&markstart, &markend);
	do_global_toggle_delete();
    }

    if (d->mode == MODE_HISTORY)
	pgn_board_update(gp, d->b, gp->hindex);
    else if (d->mode == MODE_PLAY)
	pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
}

void do_global_next_game()
{
    global_game_next_prev(1);
}

void do_global_prev_game()
{
    global_game_next_prev(0);
}

void global_find(int which)
{
    struct input_data_s *in;
    int *p;

    if (gtotal < 2)
	return;

    in = Calloc(1, sizeof(struct input_data_s));
    p = Malloc(sizeof(int));
    *p = which;
    in->data = p;
    in->efunc = do_find_game_exp;

    if (!*gameexp || which == 0) {
	construct_input(_("Find Game by Tag Expression"), NULL, 1, 0,
		_("[name expression:]value expression"), NULL, NULL, 0, in,
		INPUT_HIST_GAME_EXP, -1);
	return;
    }

    free(p);
    free(in);
    do_find_game_exp_finalize(which);
}

void do_global_find_new()
{
    global_find(0);
}

void do_global_find_next()
{
    global_find(1);
}

void do_global_find_prev()
{
    global_find(-1);
}

void do_global_game_jump()
{
    if (gtotal < 2)
	return;

    if (!keycount) {
        struct input_data_s *in;

	in = Calloc(1, sizeof(struct input_data_s));
	in->efunc = do_game_jump;
	construct_input(_("Jump to Game Number"), NULL, 1, 1, NULL, NULL, NULL, 0, in,
		-1, 0);
	return;
    }

    do_game_jump_finalize(keycount);
}

void do_global_toggle_delete()
{
    int i;

    pushkey = 0;

    if (gtotal < 2)
	return;

    if (keycount && delete_count == 0) {
	markstart = gindex;
	delete_count = keycount;
	update_status_notify(gp, "%s (delete)", status.notify);
	return;
    }

    if (markstart >= 0 && markend >= 0) {
	for (i = markstart; i < markend; i++) {
	    if (toggle_delete_flag(i)) {
		return;
	    }
	}

	gindex = (delete_count < 0) ? markstart : i - 1;
    }
    else {
	if (toggle_delete_flag(gindex))
	    return;
    }

    markstart = markend = -1;
    delete_count = 0;
    update_status_window(gp);
}

void do_global_delete_game()
{
    do_game_delete();
}

void do_global_tag_edit()
{
    struct userdata_s *d = gp->data;

    edit_tags(gp, d->b, 1);
}

void do_global_tag_view()
{
    struct userdata_s *d = gp->data;

    edit_tags(gp, d->b, 0);
}

void do_global_resume_game()
{
    struct input_data_s *in;

    in = Calloc(1, sizeof(struct input_data_s));
    in->efunc = do_load_file;
    construct_input(_("Load Filename"), NULL, 1, 1, _("Type TAB for file browser"), file_browser,
	    NULL, '\t', in, INPUT_HIST_FILE, -1);
}

void do_global_save_game()
{
    if (gtotal > 1) {
	construct_message(NULL, _("What would you like to do?"), 0, 1,
			  NULL, NULL, NULL, do_game_save_multi_confirm, 0, 0,
			  _("There is more than one game loaded. Press \"%ls\" to save the current game, \"%ls\" to save all games or any other key to cancel."),
			  current_wchar, all_wchar);
	return;
    }

    do_get_game_save_input(-1);
}

void do_global_new_game()
{
    do_new_game();
}

void do_global_copy_game()
{
    int g = gindex;
    int i, n;
    struct userdata_s *d;

    do_global_new_game();
    d = gp->data;
    n = pgn_tag_total(game[g]->tag);

    for (i = 0; i < n; i++)
	pgn_tag_add(&gp->tag, game[g]->tag[i]->name,
		game[g]->tag[i]->value);

    pgn_board_init_fen (gp, d->b, NULL);
    n = pgn_history_total(game[g]->history);

    // FIXME RAV
    for (i = 0; i < n; i++) {
	char *frfr = NULL;
	char *move = strdup (game[g]->history[i]->move);

	if (pgn_parse_move(gp, d->b, &move, &frfr) != E_PGN_OK) {
	    free (move);
	    SET_FLAG(gp->flags, GF_PERROR);
	    return;
	}

	pgn_history_add(gp, d->b, move);
	free (move);
	free(frfr);
	pgn_switch_turn(gp);
    }

    pgn_board_update(gp, d->b, pgn_history_total(gp->hp));
}

void do_global_new_all()
{
    construct_message(NULL, _("[ Yes or No ]"), 1, 1, NULL, NULL, NULL,
	    do_new_game_from_scratch, 0, 0, "%s", _("Really start a new game from scratch?"));
}

void do_quit(WIN *win)
{
    wchar_t str[] = { win->c, 0 };

    if (wcscmp (str, yes_wchar))
	return;

    quit = 1;
}

void do_global_quit()
{
    if (config.exitdialogbox)
	construct_message(NULL, _("[ Yes or No ]"), 1, 1, NULL, NULL, NULL,
			  do_quit, 0, 0, _("Want to Quit?"));
    else
	quit = 1;
}

void do_global_toggle_engine_window()
{
    if (!enginew) {
	enginew = newwin(LINES, COLS, 0, 0);
	enginep = new_panel(enginew);
	window_draw_title(enginew, _("Engine IO Window"), COLS, CP_MESSAGE_TITLE,
		CP_MESSAGE_BORDER);
	hide_panel(enginep);
    }

    if (panel_hidden(enginep)) {
	update_engine_window(gp);
	top_panel(enginep);
    }
    else {
	hide_panel(enginep);
    }
}

void do_global_toggle_board_details()
{
    do_board_details();
}

void do_global_toggle_strict_castling()
{
    do_toggle_strict_castling();
}

// Global and other keys.
static int globalkeys()
{
    struct userdata_s *d = gp->data;
    int i;

    /*
     * These cannot be modified and other game mode keys cannot conflict with
     * these.
     */
    switch (input_c) {
	case KEY_ESCAPE:
	    d->sp.icon = d->sp.srow = d->sp.scol = 0;
	    markend = markstart = 0;

	    if (keycount) {
		keycount = 0;
		update_status_notify(gp, NULL);
	    }

	    if (config.validmoves)
		pgn_reset_valid_moves(d->b);

	    return 1;
	case '0' ... '9':
	    i = input_c - '0';

	    if (keycount)
		keycount = keycount * 10 + i;
	    else
		keycount = i;

	    update_status_notify(gp, _("Repeat %i"), keycount);
	    return -1;
	case KEY_UP:
	    if (d->mode == MODE_HISTORY)
		return 0;

	    if (keycount)
		d->c_row += keycount;
	    else
		d->c_row++;

	    if (d->c_row > 8)
		d->c_row = 1;

	    return 1;
	case KEY_DOWN:
	    if (d->mode == MODE_HISTORY)
		return 0;

	    if (keycount) {
		d->c_row -= keycount;
		update_status_notify(gp, NULL);
	    }
	    else
		d->c_row--;

	    if (d->c_row < 1)
		d->c_row = 8;

	    return 1;
	case KEY_LEFT:
	    if (d->mode == MODE_HISTORY)
		return 0;

	    if (keycount)
		d->c_col -= keycount;
	    else
		d->c_col--;

	    if (d->c_col < 1)
		d->c_col = 8;

	    return 1;
	case KEY_RIGHT:
	    if (d->mode == MODE_HISTORY)
		return 0;

	    if (keycount)
		d->c_col += keycount;
	    else
		d->c_col++;

	    if (d->c_col > 8)
		d->c_col = 1;

	    return 1;
	case KEY_RESIZE:
	    return 1;
	case 0:
	default:
	    for (i = 0; global_keys[i]; i++) {
		if (input_c == global_keys[i]->c && global_keys[i]->f) {
		    (*global_keys[i]->f)();
		    return 1;
		}
	    }
	    break;
    }

    return 0;
}

#ifdef WITH_LIBPERL
static void perl_error(const char *fmt, ...)
{
    va_list ap;
    char *buf;

    va_start(ap, fmt);
    vasprintf(&buf, fmt, ap);
    va_end(ap);

    message(ERROR_STR, ANY_KEY_STR, "%s", buf);
    free(buf);
}

static void do_perl_finalize(WIN *win)
{
    struct input_data_s *in = win->data;
    GAME g = in->data;
    struct userdata_s *d = g->data;
    char *filename;
    char *result = NULL;
    char *arg = NULL;
    int n;

    asprintf(&filename, "%s/perl.pl", config.datadir);

    if (!in->str)
	goto done;

    if (perl_init_file(filename, perl_error))
	goto done;

    arg = pgn_game_to_fen(g, d->b);

    if (perl_call_sub(trim(in->str), arg, &result))
	goto done;

    d->perlfen = pgn_game_to_fen(g, d->b);
    d->perlflags = g->flags;

    if (pgn_board_init_fen(g, d->b, result) != E_PGN_OK) {
	message(ERROR_STR, ANY_KEY_STR, "%s", _("FEN parse error."));
	pgn_board_init_fen(g, d->b, d->perlfen);
	g->flags = d->perlflags;
	free(d->perlfen);
	d->perlfen = NULL;
	goto done;
    }

    SET_FLAG(d->flags, CF_PERL);
    n = pgn_tag_find(g->tag, "FEN");

    if (n != E_PGN_ERR)
	d->oldfen = strdup(g->tag[n]->value);

    pgn_tag_add(&g->tag, "FEN", result);
    update_status_notify(g, "%s", ANY_KEY_STR);
    update_all(g);

done:
    free(result);
    free(arg);
    free(in->str);
    free(in);
    free(filename);
}

void do_global_perl()
{
    struct input_data_s *in;

    in = Calloc(1, sizeof(struct input_data_s));
    in->data = gp;
    in->efunc = do_perl_finalize;
    construct_input(_("PERL Subroutine Filter"), NULL, 1, 0, NULL, NULL, NULL, 0, in, INPUT_HIST_PERL, -1);
}
#endif

/*
 * A macro may contain a key that belongs to another macro so macro_match will
 * need to be updated to the new index of the matching macro.
 */
static void find_macro(struct userdata_s *d)
{
    int i;

    /*
     * Macros can't contain macros when in a window.
     */
    if (wins)
	return;

again:
    for (i = 0; macros[i]; i++) {
	if ((macros[i]->mode == -1 || macros[i]->mode == d->mode) &&
		input_c == macros[i]->c) {
	    input_c = macros[i]->keys[macros[i]->n++];

	    if (!macro_depth_n && macro_match > -1) {
		macro_depth = realloc(macro_depth, (macro_depth_n + 1) * sizeof(int));
		macro_depth[macro_depth_n++] = macro_match;
	    }

	    macro_depth = realloc(macro_depth, (macro_depth_n + 1) * sizeof(int));
	    macro_depth[macro_depth_n++] = i;
	    macro_match = i;
	    goto again;
	}
    }
}

/*
 * Resets the position in each macro to the first key.
 */
static void reset_macros()
{
    int i;
    struct userdata_s *d = gp->data;

again:
    if (macro_depth_n > 0) {
	macro_depth_n--;
	macro_match = macro_depth[macro_depth_n];

	if (macros[macro_match]->n >= macros[macro_match]->total)
	    goto again;

	input_c = macros[macro_match]->keys[macros[macro_match]->n++];
	find_macro(d);
	return;
    }

    for (i = 0; macros[i]; i++)
	macros[i]->n = 0;

    free(macro_depth);
    macro_depth = NULL;
    macro_depth_n = 0;
    macro_match = -1;
}

void game_loop()
{
    struct userdata_s *d;

    macro_match = -1;
    gindex = gtotal - 1;
    gp = game[gindex];
    d = gp->data;

    if (pgn_history_total(gp->hp))
	d->mode = MODE_HISTORY;
    else {
         d->mode = MODE_PLAY;
	 d->play_mode = PLAY_HE;
    }

	d->rotate = FALSE;
	d->go_move = 0;
	d->pm_undo = FALSE;
	d->pm_frfr[0] = '\0';

    if (d->mode == MODE_HISTORY)
	pgn_board_update(gp, d->b, pgn_history_total(gp->hp));

    update_status_notify(gp, "%s", _("Type F1 for help"));
    movestep = 2;
    flushinp();
    update_all(gp);
    wtimeout(boardw, WINDOW_TIMEOUT);

    while (!quit) {
	int n = 0, i;
	char fdbuf[8192] = {0};
	int len;
	struct timeval tv = {0, 0};
	fd_set rfds, wfds;
	WIN *win = NULL;
	WINDOW *wp = NULL;

	FD_ZERO(&rfds);
	FD_ZERO(&wfds);

	for (i = 0; i < gtotal; i++) {
	    d = game[i]->data;

	    if (d->engine && d->engine->pid != -1) {
		if (d->engine->fd[ENGINE_IN_FD] > 2) {
		    if (d->engine->fd[ENGINE_IN_FD] > n)
			n = d->engine->fd[ENGINE_IN_FD];

		    FD_SET(d->engine->fd[ENGINE_IN_FD], &rfds);
		}

		if (d->engine->fd[ENGINE_OUT_FD] > 2) {
		    if (d->engine->fd[ENGINE_OUT_FD] > n)
			n = d->engine->fd[ENGINE_OUT_FD];

		    FD_SET(d->engine->fd[ENGINE_OUT_FD], &wfds);
		}
	    }
	}

	if (n) {
	    if ((n = select(n + 1, &rfds, &wfds, NULL, &tv)) > 0) {
		for (i = 0; i < gtotal; i++) {
		    d = game[i]->data;

		    if (d->engine && d->engine->pid != -1) {
			if (FD_ISSET(d->engine->fd[ENGINE_IN_FD], &rfds)) {
			    len = read(d->engine->fd[ENGINE_IN_FD], fdbuf,
				    sizeof(fdbuf));

			    if (len > 0) {
				if (d->engine->iobuf)
				    d->engine->iobuf = Realloc(d->engine->iobuf, d->engine->len + len + 1);
				else
				    d->engine->iobuf = Calloc(1, len + 1);

				memcpy(&(d->engine->iobuf[d->engine->len]), &fdbuf, len);
				d->engine->len += len;
				d->engine->iobuf[d->engine->len] = 0;

				/*
				 * The fdbuf is full or no newline
				 * was found. So we'll append the next
				 * read() to this games buffer.
				 */
				if (d->engine->iobuf[d->engine->len - 1] != '\n')
				    continue;

				parse_engine_output(game[i], d->engine->iobuf);
				free(d->engine->iobuf);
				d->engine->iobuf = NULL;
				d->engine->len = 0;
			    }
			    else if (len == -1) {
				if (errno != EAGAIN) {
				    cmessage(ERROR_STR, ANY_KEY_STR, "Engine read(): %s",
					    strerror(errno));
				    waitpid(d->engine->pid, &n, 0);
				    free(d->engine);
				    d->engine = NULL;
				    break;
				}
			    }
			}

			if (FD_ISSET(d->engine->fd[ENGINE_OUT_FD], &wfds)) {
			    if (d->engine->queue)
				send_engine_command(game[i]);
			}
		    }
		}
	    }
	    else {
		if (n == -1)
		    cmessage(ERROR_STR, ANY_KEY_STR, "select(): %s", strerror(errno));
		/* timeout */
	    }
	}

	gp = game[gindex];
	d = gp->data;

	/*
	 * This is needed to detect terminal resizing.
	 */
	doupdate();
	if (LINES != LINES_OLD || COLS != COLS_OLD) {
		COLS_OLD = COLS;
		LINES_OLD = LINES;
		do_window_resize();
	}

	/*
	 * Finds the top level window in the window stack so we know what
	 * window the wget_wch()'ed key belongs to.
	 */
	if (wins) {
	    for (i = 0; wins[i]; i++);
	    win = wins[i-1];
	    wp = win->w;
	    wtimeout(wp, WINDOW_TIMEOUT);
	}
	else
	    wp = boardw;

	if (!i && pushkey)
	    input_c = pushkey;
	else {
	    if (!pushkey) {
		if (macros && macro_match >= 0) {
		    if (macros[macro_match]->n >= macros[macro_match]->total)
			reset_macros();
		    else {
			input_c = macros[macro_match]->keys[macros[macro_match]->n++];
			find_macro(d);
		    }
		}
		else {
		  if (wget_wch(wp, &input_c) == ERR || input_c == KEY_RESIZE)
		      continue;
		}
	    }
	    else
		input_c = pushkey;

	    if (win) {
		win->c = input_c;

		/*
		 * Run the function associated with the window. When the
		 * function returns 0 win->efunc is ran (if not NULL) with
		 * win as the one and only parameter. Then the window is
		 * destroyed.
		 *
		 * The exit function may create another window which will
		 * mess up the window stack when window_destroy() is called.
		 * So don't destory the window until the top window is
		 * destroyable. See window_destroy().
		 */
		if ((*win->func)(win) == 0) {
		    if (win->efunc)
			(*win->efunc)(win);

		    win->keep = 1;
		    window_destroy(win);
		    update_all(gp);
		}

		continue;
	    }
	}

	if (!keycount && status.notify)
	    update_status_notify(gp, NULL);

#ifdef WITH_LIBPERL
	if (TEST_FLAG(d->flags, CF_PERL)) {
	    CLEAR_FLAG(d->flags, CF_PERL);
	    pgn_board_init_fen(gp, d->b, d->perlfen);
	    gp->flags = d->perlflags;
	    free(d->perlfen);
	    pgn_tag_add(&gp->tag, "FEN", d->oldfen);
	    free(d->oldfen);
	    d->perlfen = d->oldfen = NULL;
	    update_all(gp);
	    continue;
	}
#endif

	if (macros && macro_match < 0)
	    find_macro(d);

	if ((n = globalkeys()) == 1) {
	    if (macro_match == -1)
		keycount = 0;

	    goto refresh;
	}
	else if (n == -1)
	    goto refresh;

	switch (d->mode) {
	    case MODE_EDIT:
		for (i = 0; edit_keys[i]; i++) {
		    if (input_c == edit_keys[i]->c) {
			(*edit_keys[i]->f)();
			break;
		    }
		}
		break;
	    case MODE_PLAY:
		for (i = 0; play_keys[i]; i++) {
		    if (input_c == play_keys[i]->c) {
			(*play_keys[i]->f)();
			goto done;
		    }
		}

		do_play_config_command();
		break;
	    case MODE_HISTORY:
		for (i = 0; history_keys[i]; i++) {
		    if (input_c == history_keys[i]->c) {
			(*history_keys[i]->f)();
			break;
		    }
		}
		break;
	    default:
		break;
	}

done:
	if (keycount)
	    update_status_notify(gp, NULL);

	keycount = 0;

refresh:
	update_all(gp);
    }
}

void usage(const char *pn, int ret)
{
    fprintf((ret) ? stderr : stdout, "%s%s",
#ifdef DEBUG
    _(
    "Usage: cboard [-hvCD] [-u [N]] [-p [-VtRSE] <file>]\n"
    "  -D  Dump libchess debugging info to \"libchess.debug\" (stderr)\n"),
#else
	_(
    "Usage: cboard [-hvC] [-u [N]] [-p [-VtRSE] <file>]\n"),
#endif
    _(
    "  -p  Load PGN file.\n"
    "  -V  Validate a game file.\n"
    "  -S  Validate and output a PGN formatted game.\n"
    "  -R  Like -S but write a reduced PGN formatted game.\n"
    "  -t  Also write custom PGN tags from config file.\n"
    "  -E  Stop processing on file parsing error (overrides config).\n"
    "  -C  Enable strict castling (overrides config).\n"
    "  -u  Enable/disable UTF-8 pieces (1=enable, 0=disable, overrides config).\n"
    "  -v  Version information.\n"
    "  -h  This help text.\n"));

    exit(ret);
}

void cleanup_all()
{
    int i;

    stop_clock();
    free_userdata();
    pgn_free_all();
    free(config.engine_cmd);
    free(config.pattern);
    free(config.ccfile);
    free(config.nagfile);
    free(config.configfile);

    if (config.keys) {
	for (i = 0; config.keys[i]; i++) {
	    free(config.keys[i]->str);
	    free(config.keys[i]);
	}

	free(config.keys);
    }

    if (config.einit) {
	for (i = 0; config.einit[i]; i++)
	    free(config.einit[i]);

	free(config.einit);
    }

    if (config.tag)
	pgn_tag_free(config.tag);

    free(config.datadir);

    if (curses_initialized) {
	del_panel(boardp);
	del_panel(historyp);
	del_panel(statusp);
	del_panel(tagp);
	delwin(boardw);
	delwin(historyw);
	delwin(statusw);
	delwin(tagw);

	if (enginew) {
	    del_panel(enginep);
	    delwin(enginew);
	}

	endwin();
    }

#ifdef WITH_LIBPERL
    perl_cleanup();
#endif
}

static void signal_save_pgn(int sig)
{
    char *buf;
    time_t now;
    char *p = config.savedirectory ? config.savedirectory : config.datadir;

    time(&now);
    asprintf(&buf, "%s/signal-%i-%li.pgn", p, sig, now);

    if (do_game_write(buf, "w", 0, gtotal)) {
	cmessage(ERROR_STR, ANY_KEY_STR, "%s: %s", p, strerror(errno));
	update_status_notify(gp, "%s", _("Save game failed."));
    }

    free(buf);
    quit = 1;
}

void catch_signal(int which)
{
    switch (which) {
	case SIGALRM:
	    update_clocks();
	    break;
	case SIGPIPE:
	    if (which == SIGPIPE && quit)
		break;

	    if (which == SIGPIPE)
		cmessage(NULL, ANY_KEY_STR, "%s", _("Broken pipe. Quitting."));

	    cleanup_all();
	    exit(EXIT_FAILURE);
	    break;
	case SIGSTOP:
	    savetty();
	    break;
	case SIGCONT:
	    resetty();
	    do_window_resize ();
	    keypad(boardw, TRUE);
	    break;
	case SIGINT:
	    quit = 1;
	    break;
	case SIGTERM:
	    signal_save_pgn(which);
	    break;
	default:
	    break;
    }
}

void loading_progress(long total, long offset)
{
    int n = (100 * (offset / 100) / (total / 100));

    if (curses_initialized)
	update_loading_window(n);
    else {
        fprintf(stderr, _("Loading... %i%% (%i games)%c"), n, gtotal, '\r');
	fflush(stderr);
    }
}

static void set_defaults()
{
    set_config_defaults();
    set_default_keys();
    filetype = FILE_NONE;
    pgn_config_set(PGN_PROGRESS, 1024);
    pgn_config_set(PGN_PROGRESS_FUNC, loading_progress);
}

int main(int argc, char *argv[])
{
    int opt;
    struct stat st;
    char buf[FILENAME_MAX];
    char datadir[FILENAME_MAX];
    int ret = EXIT_SUCCESS;
    int validate_only = 0, validate_and_write = 0;
    int write_custom_tags = 0;
    int i = 0;
    PGN_FILE *pgn;
    int utf8_pieces = -1;

    setlocale (LC_ALL, "");
    bindtextdomain ("cboard", LOCALE_DIR);
    textdomain ("cboard");

    /* Solaris 5.9 */
#ifndef HAVE_PROGNAME
    __progname = argv[0];
#endif

    if ((config.pwd = getpwuid(getuid())) == NULL)
	err(EXIT_FAILURE, "getpwuid()");

    snprintf(datadir, sizeof(datadir), "%s/.cboard", config.pwd->pw_dir);
    config.datadir = strdup(datadir);
    snprintf(buf, sizeof(buf), "%s/cc.data", datadir);
    config.ccfile = strdup(buf);
    snprintf(buf, sizeof(buf), "%s/nag.data", datadir);
    config.nagfile = strdup(buf);
    snprintf(buf, sizeof(buf), "%s/config", datadir);
    config.configfile = strdup(buf);

    if (stat(datadir, &st) == -1) {
	if (errno == ENOENT) {
	    if (mkdir(datadir, 0755) == -1)
		err(EXIT_FAILURE, "%s", datadir);
	}
	else
	    err(EXIT_FAILURE, "%s", datadir);

	stat(datadir, &st);
    }

    if (!S_ISDIR(st.st_mode))
	errx(EXIT_FAILURE, "%s: %s", datadir, _("Not a directory."));

    set_defaults();

#ifdef DEBUG
    while ((opt = getopt(argc, argv, "DCEVtSRhp:vu::")) != -1) {
#else
    while ((opt = getopt(argc, argv, "ECVtSRhp:vu::")) != -1) {
#endif
	switch (opt) {
#ifdef DEBUG
	    case 'D':
		unlink("libchess.debug");
		pgn_config_set(PGN_DEBUG, 1);
		break;
#endif
	    case 'C':
		pgn_config_set(PGN_STRICT_CASTLING, 1);
		break;
	    case 't':
		write_custom_tags = 1;
		break;
	    case 'E':
		i = 1;
		break;
	    case 'R':
		pgn_config_set(PGN_REDUCED, 1);
	    case 'S':
		validate_and_write = 1;
	    case 'V':
		validate_only = 1;
		break;
	    case 'v':
		printf("%s (%s)\n%s\n", PACKAGE_STRING, curses_version(),
			COPYRIGHT);
		exit(EXIT_SUCCESS);
	    case 'p':
		filetype = FILE_PGN;
		strncpy(loadfile, optarg, sizeof(loadfile));
		loadfile[sizeof(loadfile)-1] = 0;
		break;
	    case 'u':
	        utf8_pieces = optarg ? atoi (optarg): 1;
		break;
	    case 'h':
	    default:
		usage(argv[0], EXIT_SUCCESS);
	}
    }

    if ((validate_only || validate_and_write) && !*loadfile)
	usage(argv[0], EXIT_FAILURE);

    if (access(config.configfile, R_OK) == 0)
	parse_rcfile(config.configfile);

    if (i)
	pgn_config_set(PGN_STOP_ON_ERROR, 1);

    signal(SIGPIPE, catch_signal);
    signal(SIGCONT, catch_signal);
    signal(SIGSTOP, catch_signal);
    signal(SIGINT, catch_signal);
    signal(SIGALRM, catch_signal);
    signal(SIGTERM, catch_signal);

    srandom(getpid());

    switch (filetype) {
	case FILE_PGN:
	    if (pgn_open(loadfile, "r", &pgn) != E_PGN_OK)
		err(EXIT_FAILURE, "%s", loadfile);

	    ret = pgn_parse(pgn);
	    pgn_close(pgn);
	    break;
	case FILE_FEN:
	    //ret = parse_fen_file(loadfile);
	    break;
	case FILE_EPD: // Not implemented.
        case FILE_NONE:
	default:
	    // No file specified. Empty game.
	    ret = pgn_parse(NULL);
	    gp = game[gindex];
	    add_custom_tags(&gp->tag);
	    break;
    }

    if (validate_only || validate_and_write) {
	if (validate_and_write) {
	    if (pgn_open("-", "r", &pgn) != E_PGN_OK)
		err(EXIT_FAILURE, "pgn_open()");

	    for (i = 0; i < gtotal; i++) {
		if (write_custom_tags)
		    add_custom_tags(&game[i]->tag);

		pgn_write(pgn, game[i]);
	    }

	    pgn_close(pgn);

	    fm_loaded_file = TRUE;
	}

	cleanup_all();
	exit(ret);
    }
    else if (ret == E_PGN_ERR)
	exit(ret);

    if (utf8_pieces != -1)
        config.utf8_pieces = utf8_pieces;

    init_wchar_pieces ();
    yes_wchar = str_to_wchar (_("y"));
    all_wchar = str_to_wchar (_("a"));
    overwrite_wchar = str_to_wchar (_("o"));
    resume_wchar = str_to_wchar (_("r"));
    current_wchar = str_to_wchar (_("c"));
    append_wchar = str_to_wchar (_("a"));
    translatable_tag_names[0] = _("Event");
    translatable_tag_names[1] = _("Site");
    translatable_tag_names[2] = _("Date");
    translatable_tag_names[3] = _("Round");
    translatable_tag_names[4] = _("White");
    translatable_tag_names[5] = _("Black");
    translatable_tag_names[6] = _("Result");
    init_userdata();

    /*
     * This fixes window resizing in an xterm.
     */
    if (getenv("DISPLAY") != NULL) {
	putenv("LINES=");
	putenv("COLUMNS=");
    }

    if (initscr() == NULL)
	errx(EXIT_FAILURE, "%s", _("Could not initialize curses."));
    else
	curses_initialized = 1;

    if (LINES < 23 || COLS < 74) {
	endwin();
	errx(EXIT_FAILURE, _("Need at least an 74x23 terminal."));
    }

    COLS_OLD = COLS;
    LINES_OLD = LINES;

    if (has_colors() == TRUE && start_color() == OK)
	init_color_pairs();

    boardw = newwin(BOARD_HEIGHT, BOARD_WIDTH, 0, COLS - BOARD_WIDTH);
    boardp = new_panel(boardw);
    historyw = newwin(HISTORY_HEIGHT, HISTORY_WIDTH, LINES - HISTORY_HEIGHT,
	    COLS - HISTORY_WIDTH);
    historyp = new_panel(historyw);
    statusw = newwin(STATUS_HEIGHT, STATUS_WIDTH, 0, 0);
    statusp = new_panel(statusw);
    tagw = newwin(TAG_HEIGHT, TAG_WIDTH, STATUS_HEIGHT + 1, 0);
    tagp = new_panel(tagw);
    keypad(boardw, TRUE);
//  leaveok(boardw, TRUE);
    leaveok(tagw, TRUE);
    leaveok(statusw, TRUE);
    leaveok(historyw, TRUE);
    curs_set(0);
    cbreak();
    noecho();
    draw_window_decor();
    game_loop();
    cleanup_all();
    free (w_pawn_wchar);
    free (w_rook_wchar);
    free (w_bishop_wchar);
    free (w_knight_wchar);
    free (w_queen_wchar);
    free (w_king_wchar);
    free (b_pawn_wchar);
    free (b_rook_wchar);
    free (b_bishop_wchar);
    free (b_knight_wchar);
    free (b_queen_wchar);
    free (b_king_wchar);
    free (empty_wchar);
    free (enpassant_wchar);
    free (yes_wchar);
    free (all_wchar);
    free (overwrite_wchar);
    free (resume_wchar);
    free (current_wchar);
    free (append_wchar);
    free (status.notify);
    exit(EXIT_SUCCESS);
}
