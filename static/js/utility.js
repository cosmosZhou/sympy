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

function this_phrases() {
	return ['apply', 'args', 'expr', 'lhs', 'rhs', 'find'];
}

function hint(cm, options) {
	var Pos = CodeMirror.Pos;
	return new Promise(function(accept) {
		var cur = cm.getCursor();
		var token = cm.getTokenAt(cur);
		var tokenString = token.string;
		console.log('tokenString = ' + tokenString);

		var text = cm.getLine(cur.line);
		text = text.slice(0, cur.ch);
		var prefix = text.match(/[\w.]+$/)[0];

		var sympy = sympy_user();
		var url = `/${sympy}/php/request/`;

		var kwargs;
		if (tokenString == '.' || prefix.startsWith('.')) {
			token.start += 1;

			switch (prefix) {
				case 'Eq.':
					var list = new Set();
					var self = options.context;
					for (let editor of self.$parent.renderProve) {
						var text = editor.editor.getValue();
						for (var text of text.split("\n")) {
							console.log(text);
							for (let m of text.matchAll(/\bEq\.(\w+)/g)) {
								list.add(m[1]);
							}
						}
					}

					list = Array.from(list);
					list.sort();
					console.log('list = ' + list);
					return accept({
						list: list,
						from: Pos(cur.line, token.start),
						to: Pos(cur.line, token.end)
					});
				case '.':
					if (text.match(/\bEq\[-?\d+\]\.$/)) {
						var list = ['this', 'subs', 'variable', 'reversed', 'lhs', 'rhs'];
						return accept({
							list: list,
							from: Pos(cur.line, token.start),
							to: Pos(cur.line, token.end)
						});
					}
					else if (text.match(/\w+\.args\[-?\d+\]\.$/) || text.match(/\.find\(.+\)\.$/)) {
						return accept({
							list: this_phrases(),
							from: Pos(cur.line, token.start),
							to: Pos(cur.line, token.end)
						});
					}
				case ".this.":
					if (text.match(/\bEq\[-?\d+\]\.this\.$/)) {
						return accept({
							list: this_phrases(),
							from: Pos(cur.line, token.start),
							to: Pos(cur.line, token.end)
						});
					}
				default:
					var m = prefix.match(/^\.([\w.]*\.)(\w*)$/);
					if (m) {
						var phrase, _;
						[_, prefix, phrase] = m;
						switch (prefix) {
							case "this.":
								var list = [];
								for (let word of this_phrases()) {
									if (word.startsWith(phrase)) {
										list.push(word);
									}
								}
								token.start -= 1;
								return accept({
									list: list,
									from: Pos(cur.line, token.start),
									to: Pos(cur.line, token.end)
								});
							default:
								if (!phrase) {
									var list = prefix.split('.');
									if (list[list.length - 2] == 'apply') {
										break;
									}
									
									return accept({
										list: this_phrases(),
										from: Pos(cur.line, token.start),
										to: Pos(cur.line, token.end)
									});
								}
								break;
						}
					}

					break;
			}

			kwargs = { prefix: prefix, phrase: '' };
			url += `suggest.php`;
		}
		else {
			if (prefix.indexOf('.') >= 0) {
				var m = prefix.match(/([\w.]*\.)(\w*)$/);
				var phrase, _;
				[_, prefix, phrase] = m;
				kwargs = { prefix: prefix, phrase: phrase };
				m = prefix.match(/^(\w*)\.$/);
				if (m) {
					switch (m[1]) {
						case 'algebra':
						case 'calculus':
						case 'discrete':
						case 'geometry':
						case 'keras':
						case 'sets':
						case 'stats':
							url += `suggest.php`;
							break;
						default:
							kwargs = { prefix: phrase };
							url += `hint.php`;
							break;
					}
				}
				else
					url += `suggest.php`;
			}
			else {
				kwargs = { prefix: prefix };
				url += `hint.php`;
			}
		}

		form_post(url, kwargs).then(list => {

			// Find the token at the cursor
			console.log('list = ' + list);
			return accept({
				list: list,
				from: Pos(cur.line, token.start),
				to: Pos(cur.line, token.end)
			});
		}).catch(fail);
	});
}

function sympy_user() {
	var href = location.href;
	return href.match(/([^\/]+)\/(?:axiom.php|run.py|php\/\w+\.php)\b/)[1];
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

		'Alt': function(cm) {
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

function textFocused(text, selectionStart) {
	console.log("selectionStart = " + selectionStart);

	for (; selectionStart < text.length; ++selectionStart) {
		var char = text[selectionStart];
		if (char >= 'a' && char <= 'z' ||
			char >= 'A' && char <= 'Z' ||
			char == '_' ||
			char >= '0' && char <= '9') {
			continue;
		}
		else {
			break;
		}
	}

	var textForFocus = text.slice(0, selectionStart);
	var m = textForFocus.match(/(\w+)(?:\.\w+)*$/);
	return m[0];
}

function find_and_jump(event) {
	var self = event.target;

	var module = textFocused(self.value, self.selectionStart);
	console.log('module = ' + module);
	var href;
	var indexOfDot = module.lastIndexOf('.');
	var user = sympy_user();
	if (indexOfDot >= 0) {
		if (module.slice(indexOfDot + 1) == 'apply') {
			module = module.slice(0, indexOfDot);
			module += "&apply=0";
		}
		href = `/${user}/axiom.php?module=${module}`;
	}
	else {
		switch (module) {
			case 'algebra':
			case 'calculus':
			case 'discrete':
			case 'geometry':
			case 'keras':
			case 'sets':
			case 'stats':
				href = `/${user}/axiom.php?module=${module}`;
				break;
			default:
				href = `/${user}/axiom.php?symbol=${module}`;
		}
	}

	if (event.ctrlKey)
		location.href = href;
	else
		window.open(href);

}

function saveDocument() {
	console.log("'Ctrl-S' is pressed!");
	var module = document.querySelector('input').value;
	console.log("module = " + module);
	module = module.replace(/\./g, '/');
	console.log("module = " + module);

	var user = sympy_user();
	form.action = `/${user}/axiom.php?module=${module}`;
	console.log("form.action = " + form.action);
	console.log("save the content now");
	form.submit();
}

async function createApp(component, data, id) {
	const options = {
		moduleCache: { vue: Vue },
	
		async getFile(url) {
			const res = await fetch(url);
	
			if (!res.ok)
				throw Object.assign(new Error(res.statusText + ' ' + url), { res });
			
			return res.text();
		},
	
		addStyle(textContent) {
			document.head.insertBefore(
				Object.assign(document.createElement('style'), { textContent }),
				document.head.getElementsByTagName('style')[0] || null);
		},
	};
	
	const { loadModule } = window['vue3-sfc-loader'];
	
	id ||= 'root';
	var div = document.createElement('div');
	div.setAttribute('id', id);
	document.body.appendChild(div);
	
	var components = {};
	components[component] = await loadModule(`static/components/${component}.vue`, options);
	
	var args = [];
	for (let key in data){
		args.push(`:${key}=${key}`);	
	}
	
	var App = {
		components: components,
		
		data() {
			return data;
		},
		
		template: `<${component} ${args.join(' ')}></${component}>`,
	};
	
	var app = Vue.createApp(App);
	app.mount('#' + id);
	return app;
}

function setAttribute(self, key, value){
	while (!(key in self.$data)){
		self = self.$parent;
	}
	self.$data[key] = value;
}