
function fromTextArea(textarea, theme) {

	var _extraKeys = extraKeys();
	Object.assign(_extraKeys, {
		'Ctrl-O': function(cm) {
			console.log("'Ctrl-O' is pressed!");
			var module = form.querySelector('a').href;
			module = module.match(/=([\w.]+)/)[1];
			location.href = "/sympy/php/new.php?module=" + module;
		},

		'Ctrl-S': function(cm) {
			console.log("'Ctrl-S' is pressed!");
		},

		'Ctrl-F11': function(cm) {
			form.submit();
		},

		'Shift-Alt-W': function(cm) {
			console.log('Shift-Alt-W');
			var index = location.href.lastIndexOf('/') + 1;
			location.href = location.href.substring(0, index);
		},
	});


	return CodeMirror.fromTextArea(textarea, {
		mode: {
			name: "python",
			singleLineStringErrors: false
		},

		theme: theme || 'function',

		indentUnit: 4,

		matchBrackets: true,

		scrollbarStyle: null,

		extraKeys: _extraKeys,
		
		hintOptions: { hint: hint }
		//equivalently:		
		//CodeMirror.registerHelper("hint", "python", hint);
	});
}

function fromTextAreaOfProve() {
	var proveEditors = []
	for (let proveCode of form.querySelectorAll("textarea[name='prove[]']")) {
		proveEditors.push(fromTextArea(proveCode));
	}
	return proveEditors;
}

var app = new Vue({
	el: '#root',
	data: data,
});

if (sql) {
	execute_sql(sql);
}


var proveEditors = fromTextAreaOfProve();

proveEditors[0].focus();

var editorForApply = null;
for (let i = 0; i < proveEditors.length; ++i) {
	proveEditors[i].addKeyMap({
		'Down': function(cm) {
			var cursor = cm.getCursor();
			if (cursor.line + 1 < cm.lineCount())
				return cm.moveV(1, "line");

			cm = proveEditors[i + 1];
			cm.focus();

			if (cursor.ch == 0) {
				var linesToMove = cm.getCursor().line;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(-1, "line");
				}
			}
			else
				cm.setCursor(0, cursor.ch);
		},

		'PageDown': function(cm) {
			var cursor = cm.getCursor();
			if (cursor.line + 18 < cm.lineCount())
				return cm.moveV(1, "page");

			cm = proveEditors[i + 1];
			cm.focus();

			if (cursor.ch == 0) {
				var linesToMove = cm.getCursor().line;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(-1, "line");
				}
			}
			else
				cm.setCursor(0, cursor.ch);
		},

		'Up': function(cm) {
			var cursor = cm.getCursor();
			if (cursor.line > 0)
				return cm.moveV(-1, "line");
			if (i == 0) {
				cm = editorForApply;
			}
			else {
				cm = proveEditors[i - 1];
			}

			cm.focus();
			if (cursor.ch == 0 || i == 0) {
				var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(1, "line");
				}
			} else
				cm.setCursor(cm.lineCount() - 1, cursor.ch);
		},

		'PageUp': function(cm) {
			var cursor = cm.getCursor();
			if (cursor.line >= 18)
				return cm.moveV(-1, "page");
			if (i == 0) {
				cm = editorForApply;
			}
			else {
				cm = proveEditors[i - 1];
			}

			cm.focus();
			if (cursor.ch == 0 || i == 0) {
				var linesToMove = cm.lineCount() - cm.getCursor().line - 1;
				for (let i = 0; i < linesToMove; ++i) {
					cm.moveV(1, "line");
				}
			}
			else
				cm.setCursor(cm.lineCount() - 1, cursor.ch);
		},

		'F3': F3,
		'Ctrl-F3': cm => F3(cm, true),
	});
}

function F3(cm, newWindow) {
	var cursor = cm.getCursor();
	console.log("cursor.ch = " + cursor.ch);

	var text = cm.getLine(cursor.line);

	var selectionStart = cursor.ch;
	console.log("selectionStart = " + selectionStart);

	for (; selectionStart < text.length; ++selectionStart) {
		var char = text[selectionStart];
		if (char >= 'a' && char <= 'z' || char >= 'A' && char <= 'Z' || char == '_') {
			continue;
		}
		else {
			break;
		}
	}

	var textForFocus = text.slice(0, selectionStart);
	var m = textForFocus.match(/(\w+)(?:\.\w+)*$/);
	var module = m[0];
	console.log('module = ' + module);
	switch (module) {
		case 'apply':

			var textarea = form.querySelector('textarea[name=apply]');
			if (textarea) {
				editorForApply.focus();
			}
			else {
				var module = location.href.match(/axiom\.php\/([\w\/]+)/)[1].replace(/\//g, '.');

				request_post("/sympy/php/request.php", { apply: module }).done(code => {
					//console.log('code = ' + code);

					var textarea = document.createElement('textarea');
					textarea.name = 'apply';
					textarea.value = code;

					form.insertBefore(textarea, form.querySelector("textarea[name='prove[]']"));

					editorForApply = fromTextArea(textarea, 'eclipse');
					editorForApply.focus();

					editorForApply.addKeyMap({
						'Down': function(cm) {
							var cursor = cm.getCursor();
							if (cursor.line + 1 < cm.lineCount())
								return cm.moveV(1, "line");

							cm = proveEditors[0];
							cm.focus();
							if (cursor.ch == 0) {
								var linesToMove = cm.getCursor().line;
								for (let i = 0; i < linesToMove; ++i) {
									cm.moveV(-1, "line");
								}
							}
							else
								cm.setCursor(0, cursor.ch);
						},

						'PageDown': function(cm) {
							var cursor = cm.getCursor();
							if (cursor.line + 18 < cm.lineCount())
								return cm.moveV(1, "page");

							cm = proveEditors[0];
							cm.focus();
							if (cursor.ch == 0) {
								var linesToMove = cm.getCursor().line;
								for (let i = 0; i < linesToMove; ++i) {
									cm.moveV(-1, "line");
								}
							} else
								cm.setCursor(0, cursor.ch);
						},

						'F3': F3,
						
						'Ctrl-F3': cm => F3(cm, true),
					});


				}).fail(fail);
			}
			break;

		case 'prove':
			break;

		default:
			if (newWindow)
				window.open("/sympy/axiom.php/%s".format(module.replace(/\./g, '/')));
			else
				location.href = "/sympy/axiom.php/%s".format(module.replace(/\./g, '/'));
			break;
	}
}

function detect_cycle(module) {
	console.log("function detect_cycle(module)");
	//	underline_all_theorems();

	console.log('module = ' + module);

	request_post("/sympy/php/request.php", { detect: module }).done(theorem => {
		console.log('theorem = ' + theorem);

		//theorem = theorem.replace(/\./g, '/');		

		console.log('theorem = ' + theorem);

		for (let editor of proveEditors) {
			editor.eachLine(line => {
				var text = line.text;
				var selectionStart = text.indexOf(theorem);
				if (selectionStart >= 0) {
					console.log(text);
					var lineNo = line.lineNo();

					editor.setCursor(lineNo, selectionStart);
					editor.addSelection({ line: lineNo, ch: selectionStart }, { line: lineNo, ch: selectionStart + theorem.length });
					editor.focus();
				}
			});
		}
	}).fail(fail);
}


detect_cycle(data.module);

//http://codemirror.net/doc/manual.html