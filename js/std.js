"use strict";
String.prototype.format = function() {
	var args = arguments;
	var index = 0;
	return this.replace(/%s/g,
		function() {
			return args[index++];
		}
	);
};

String.prototype.capitalize = function(){
	return this[0].toUpperCase() + this.slice(1).toLowerCase();
};

Function.prototype.funcname = function() {
	return this.name || this.toString().match(/function\s*([^(]*)\(/)[1];
}

function strlen(s) {
	var length = 0;
	for (let i = 0; i < s.length; i++) {
		var code = s.charCodeAt(i)
		if (code < 128 || code == 0x2002)
			length += 1;
		else
			length += 2;
	}
	return length;
}

function promise(func, lapse) {
	lapse = lapse || 50;
	function execute(level) {
		if (level > 10)
			return;
		setTimeout(() => {
			try {
				func();
			} catch (error) {
				console.log(error.message);
				execute(level + 1);
			}
		}, lapse);
	}

	execute(0);
}

HTMLCollection.prototype.indexOf = function(e) {
	for (var i = 0; i < this.length; ++i) {
		if (this[i] == e)
			return i;
	}
	return -1;
};


Array.prototype.remove = function(index){
	return this.splice(index, 1);
};

Array.prototype.insert = function(index, value){
	if (index == this.length)
	 	return this.push(value);
	return this.splice(index, 1, [value, this[index]]);
};

function request_post(url, data, dataType, contentType) {
	return $.ajax({
		url: url,
		type: 'post',
		data: contentType == 'application/json' ? JSON.stringify(data) : data,
		dataType: dataType ? dataType : 'json',
		contentType: contentType ? contentType : "application/x-www-form-urlencoded",
	});
}

function post_json(url, data, dataType) {
	return $.ajax({
		url: url,
		type: 'post',
		data: JSON.stringify(data),
		dataType: dataType ? dataType : 'json',
		contentType: "application/json",
	});
}

function* matchAll(str, reg) {
	var match;
	if (!reg.global) {
		reg = RegExp(reg.source, 'g');
	}

	while (match = reg.exec(str)) {
		yield match;
	}
}

function fail(errInfo, errType, errDescription) {
	if (errInfo.responseText) {
		console.log('debugging info = ');
		console.log(errInfo);
		console.log(errType);
		console.log(errDescription);
	}
}

