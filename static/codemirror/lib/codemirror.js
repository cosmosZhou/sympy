function global_assignment(object){
	Object.assign(globalThis, object);
	/*for (let key in object) {
		globalThis[key] = object[key];
	}*/	
}

import * as browser from '../src/util/browser.js';
global_assignment(browser);

import * as dom from '../src/util/dom.js'; 
global_assignment(dom);

import * as misc from '../src/util/misc.js'; 
global_assignment(misc);

import * as bidi from '../src/util/bidi.js';
global_assignment(bidi);

import * as event from '../src/util/event.js';
global_assignment(event);

import * as feature_detection from '../src/util/feature_detection.js';
global_assignment(feature_detection);

import * as modes from '../src/modes.js';
global_assignment(modes);

import StringStream from '../src/util/StringStream.js';

import * as utils_line from '../src/line/utils_line.js';
global_assignment(utils_line);

import * as line_pos from '../src/line/pos.js';
global_assignment(line_pos);

import * as line_highlight from '../src/line/highlight.js';
global_assignment(line_highlight);

import * as line_saw_special_spans from '../src/line/saw_special_spans.js';
global_assignment(line_saw_special_spans);

import * as line_spans from '../src/line/spans.js';
global_assignment(line_spans);

import * as line_data from '../src/line/line_data.js';
global_assignment(line_data);

import * as operation_group from '../src/util/operation_group.js';
global_assignment(operation_group);

import * as update_line from '../src/display/update_line.js';
global_assignment(update_line);

import * as measurement_widgets from '../src/measurement/widgets.js';
global_assignment(measurement_widgets);

import * as position_measurement from '../src/measurement/position_measurement.js';
global_assignment(position_measurement);

import * as view_tracking from '../src/display/view_tracking.js';
global_assignment(view_tracking);

import * as display_selection from '../src/display/selection.js';
global_assignment(display_selection);

import * as display_focus from '../src/display/focus.js';
global_assignment(display_focus);

import * as update_lines from '../src/display/update_lines.js';
global_assignment(update_lines);

import * as display_scrolling from '../src/display/scrolling.js';
global_assignment(display_scrolling);

import * as display_scrollbars from '../src/display/scrollbars.js';
global_assignment(display_scrollbars);

import * as display_operations from '../src/display/operations.js';
global_assignment(display_operations);

import * as display_highlight_worker from '../src/display/highlight_worker.js';
global_assignment(display_highlight_worker);

import * as update_display from '../src/display/update_display.js';
global_assignment(update_display);

import * as display_line_numbers from '../src/display/line_numbers.js';
global_assignment(display_line_numbers);

import * as display_gutters from '../src/display/gutters.js';
global_assignment(display_gutters);

import {Display} from '../src/display/Display.js';

import * as display_scroll_events from '../src/display/scroll_events.js';
global_assignment(display_scroll_events);

import * as model_selection from '../src/model/selection.js';
global_assignment(model_selection);

import * as model_change_measurement from '../src/model/change_measurement.js';
global_assignment(model_change_measurement);

import * as display_mode_state from '../src/display/mode_state.js';
global_assignment(display_mode_state);

import * as model_document_data from '../src/model/document_data.js';
global_assignment(model_document_data);

import * as model_history from '../src/model/history.js';
global_assignment(model_history);

import * as model_selection_updates from '../src/model/selection_updates.js';
global_assignment(model_selection_updates);

import * as model_changes from '../src/model/changes.js';
global_assignment(model_changes);

import * as model_chunk from '../src/model/chunk.js';
global_assignment(model_chunk);

import * as model_line_widget from '../src/model/line_widget.js';
global_assignment(model_line_widget);

import * as model_mark_text from '../src/model/mark_text.js';
global_assignment(model_mark_text);

import Doc from '../src/model/Doc.js';

import * as edit_drop_events from '../src/edit/drop_events.js';
global_assignment(edit_drop_events);

import * as edit_global_events from '../src/edit/global_events.js';
global_assignment(edit_global_events);

import {keyNames} from '../src/input/keynames.js';

import * as input_keymap from '../src/input/keymap.js';
global_assignment(input_keymap);

import {deleteNearSelection} from '../src/edit/deleteNearSelection.js';

import * as input_movement from '../src/input/movement.js';
global_assignment(input_movement);

import {commands} from '../src/edit/commands.js';

import * as edit_key_events from '../src/edit/key_events.js';
global_assignment(edit_key_events);

import * as edit_mouse_events from '../src/edit/mouse_events.js';
global_assignment(edit_mouse_events);

import {themeChanged} from '../src/edit/utils.js';

import * as edit_options from '../src/edit/options.js';
global_assignment(edit_options);

import * as edit_CodeMirror from '../src/edit/CodeMirror.js';
global_assignment(edit_CodeMirror);

import {indentLine} from '../src/input/indent.js';

import * as input_input from '../src/input/input.js';
global_assignment(input_input);

import addEditorMethods from '../src/edit/methods.js';

import ContentEditableInput from '../src/input/ContentEditableInput.js';

import {fromTextArea} from '../src/edit/fromTextArea.js';

import {addLegacyProps} from '../src/edit/legacy.js';

import {CodeMirror} from '../src/edit/main.js';

(function(global, factory) {
	typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory() :
		typeof define === 'function' && define.amd ? define(factory) :
			(global = global || self, global.CodeMirror = factory());
}(this, (function() {
	'use strict';
	return CodeMirror;
})));
