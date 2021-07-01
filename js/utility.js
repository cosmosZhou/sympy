"use strict";

function getTextWidth(str) {
	let result = 0;
	let div = document.createElement("div");
	div.setAttribute('class', "Consolas");
	// div.style.fontStyle = 'normal';
	// div.style.fontSize = "1em";
	// div.style.fontWeight = "normal";
	// div.style.fontFamily = "Consolas";

	div.style.backgroundColor = 'inherit';
	div.style.borderStyle = 'none';
	div.style.outline = 'none';

	div.style.opacity = 0;
	div.style.position = "absolute";
	div.style.whiteSpace = "nowrap";

	div.innerText = str;
	document.body.append(div);
	result = div.getBoundingClientRect().width;
	div.remove();
	return result;
}

function underline_all_theorems() {
	//globals definition go here:
	var char_width = getTextWidth("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ") / 52;

	for (let input of document.querySelectorAll('input')) {
		if (input.className)
			continue;

		var statement = input.value;

		var div = input.parentElement;
		// console.log('statement = ' + statement);
		var index = 0;
		var previousTheoremLength = 0;
		for (let theorem of statement.matchAll(/(?:algebra|sets|calculus|discrete|geometry|keras|stats)(?:\.\w+)+/g)) {
			theorem = theorem[0];
			if (theorem.endsWith('.apply')) {
				theorem = theorem.substring(0, theorem.length - 6);
			}

			var previousIndex = index;
			index = statement.indexOf(theorem, index + 1);

			// console.log('theorem = ' + theorem);
			// console.log('index = ' + index);

			var a = document.createElement('a');

			a.style.marginLeft = '%spx'.format((index - previousIndex - previousTheoremLength) * char_width);
			a.href = "/sympy/axiom.php/%s".format(theorem.replace(/\./g, "/"));
			a.innerHTML = "-".repeat(theorem.length);

			if (!previousIndex) {
				div.appendChild(document.createElement('br'));
			}

			div.appendChild(a);
			previousTheoremLength = theorem.length;
		}
	}
}

function execute_sql(sqlFile) {
	console.log(`function execute_sql(${sqlFile})`);

	request_post("/sympy/php/request/execute.php", { sqlFile: sqlFile }).done(res => {
		console.log('success code = ');
		console.log(res);
	}).fail(fail);
}

function locate_form(activeElement) {
	var form = activeElement || document.activeElement;
	while (form.tagName != 'FORM') {
		// console.log('form.tagName = ' + form.tagName);
		// console.log('form = ');
		// console.log(form);

		form = form.parentElement;
		if (form == null)
			return;
	}

	return form;
}

function submit(activeElement) {
	var form = locate_form(activeElement);

	for (var child of form.children) {
		console.log(child);
		if (child.type == 'submit') {
			child.click();
			break;
		}
	}

	form.submit();
}

/**
 * adjust height of codemirror
 * 
 * @param cm
 * @param height
 */
function resizeHeight(cm, h) {
	var wrap = cm.getWrapperElement();
	var h = h || 200;
	var appHeight = cm.getScrollInfo().height > h ? h + 'px' : 'auto';
	wrap.style.height = appHeight;
	cm.refresh();
}

function hint(cm, options) {
	return new Promise(function(accept) {
		var cur = cm.getCursor();
		var token = cm.getTokenAt(cur);
		var tokenString = token.string;
		console.log('tokenString = ' + tokenString);
		
		var text = cm.getLine(cur.line);
		var prefix = text.slice(0, cur.ch).match(/[\w.]+$/)[0];

		var sympy = sympy_user();
		var url = `/${sympy}/php/request/`;

		if (tokenString == '.') {

			token.start += 1;
			var kwargs = { prefix: prefix, phrase: '' };
			url += `suggest.php`;
		}
		else {
			if (prefix.indexOf('.') >= 0) {
				var m = prefix.match(/([\w.]+\.)(\w*)$/);
				var phrase, _;
				[_, prefix, phrase] = m;
				var kwargs = { prefix: prefix, phrase: phrase };
				url += `suggest.php`;
			}
			else {
				var kwargs = { prefix: prefix };
				url += `hint.php`;
			}
		}

		request_post(url, kwargs).done(list => {

			// Find the token at the cursor
			console.log('list = ' + list);
			var Pos = CodeMirror.Pos;

			return accept({
				list: list,
				from: Pos(cur.line, token.start),
				to: Pos(cur.line, token.end)
			});
		}).fail(fail);
	});
}

function sympy_user() {
	var href = location.href;
	return href.match(/([^\/]+)\/(?:axiom.php|php\/\w+\.php)\b/)[1];
}


function extraKeys() {
	function open(cm, ch) {
		var [first, second] = ch.split('');
		cm.replaceSelection(first);

		var cursor = cm.getCursor();
		console.log("cursor.ch = " + cursor.ch);

		var text = cm.getLine(cursor.line);

		var selectionStart = cursor.ch;
		console.log("selectionStart = " + selectionStart);

		var left_parenthesis_count = 0;
		var left_bracket_count = 0;
		var left_brace_count = 0;
		if (text[selectionStart] != '.') {
			for (; selectionStart < text.length; ++selectionStart) {
				var char = text[selectionStart];

				if (char >= 'a' && char <= 'z' || char >= 'A' && char <= 'Z') {
					continue;
				}

				switch (char) {
					case '_':
					case '.':
						continue;
					case '(':
						++left_parenthesis_count;
						continue;
					case '[':
						++left_bracket_count;
						continue;
					case '{':
						++left_brace_count;
						continue;

					case ')':
						if (left_parenthesis_count) {
							--left_parenthesis_count;
							continue;
						}
						else
							break;
					case ']':
						if (left_bracket_count) {
							--left_bracket_count;
							continue;
						}
						else
							break;
					case '}':
						if (left_brace_count) {
							--left_brace_count;
							continue;
						}
						else
							break;
					default:
						if (left_parenthesis_count || left_bracket_count || left_brace_count)
							continue;
				}
				break;
			}
		}

		cm.setCursor(cursor.line, selectionStart);
		cm.replaceSelection(second);
		cm.setCursor(cursor.line, selectionStart);
	}

	function close(cm, ch) {
		var cursor = cm.getCursor();
		if (cursor.ch < cm.getLine(cursor.line).length && cm.getTokenAt({ ch: cursor.ch + 1, line: cursor.line }).string == ch)
			cm.setCursor(cursor.line, cursor.ch + 1);
		else
			cm.replaceSelection(ch);
	}

	return {
		Tab: function(cm) {
			cm.replaceSelection(' '.repeat(cm.getOption('indentUnit')));
		},

		'Alt-Left': function(cm) {
			history.go(-1);
		},

		'Alt-Right': function(cm) {
			history.go(1);
		},

		"[": function(cm) {
			open(cm, '[]');
		},

		"]": function(cm) {
			close(cm, ']');
		},

		"Shift-9": function(cm) {
			open(cm, '()');
		},

		"Shift-0": function(cm) {
			close(cm, ')');
		},

		"Shift-[": function(cm) {
			open(cm, '{}');
		},

		"Shift-]": function(cm) {
			close(cm, '}');
		},

		"Alt-/": function(cm) {
			return cm.showHint();
		},

		".": function(cm) {
			cm.replaceSelection('.');
			return cm.showHint();
		},
	};
}

