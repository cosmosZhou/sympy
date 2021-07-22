"use strict";
function request_get(url, data, dataType) {
	return $.ajax({
		url: url,
		type: 'get',
		data: data,
		dataType: dataType ? dataType : 'json',
	});
}

function form_post(url, data) {
	return axios.post(url, Qs.stringify(data)).then(result => result.data);
}

String.prototype.format = function() {
	var args = arguments;
	var index = 0;
	return this.replace(/%s/g,
		function() {
			return args[index++];
		}
	);
};

String.prototype.capitalize = function() {
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
		try {
			func();
		} catch (error) {
			setTimeout(() => {
				execute(level + 1);
				console.log(error.message);
				console.trace();
			}, lapse);
		}
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


Array.prototype.remove = function(index) {
	return this.splice(index, 1);
};

Array.prototype.insert = function(index, value) {
	if (index == this.length)
		return this.push(value);
	return this.splice(index, 1, [value, this[index]]);
};

Array.prototype.back = function() {
	return this[this.length - 1];
};

function post_json(url, data, dataType) {
	return $.ajax({
		url: url,
		type: 'post',
		data: JSON.stringify(data),
		dataType: dataType ? dataType : 'json',
		contentType: "application/json",
	});
}

function fail(errInfo, errType, errDescription) {
	if (errInfo.responseText) {
		console.log('debugging info = ');
		console.log(errInfo);
		console.log(errType);
		console.log(errDescription);
	}
}

/**
 * @template T
 */
class Queue {
	/**
	 * @param {Iterable<T>=} items The initial elements.
	 */
	constructor(items) {
		/** @private @type {T[]} */
		this._list = items ? Array.from(items) : [];
		/** @private @type {T[]} */
		this._listReversed = [];
	}

	/**
	 * Returns the number of elements in this queue.
	 * @returns {number} The number of elements in this queue.
	 */
	get length() {
		return this._list.length + this._listReversed.length;
	}

	isEmpty() {
		return !this.length;
	}
	/**
	 * Appends the specified element to this queue.
	 * @param {T} item The element to add.
	 * @returns {void}
	 */
	push(item) {
		this._list.push(item);
	}

	/**
	 * Retrieves and removes the head of this queue.
	 * @returns {T | undefined} The head of the queue of `undefined` if this queue is empty.
	 */
	pop() {
		if (this._listReversed.length === 0) {
			if (this._list.length === 0) return undefined;
			if (this._list.length === 1) return this._list.pop();
			if (this._list.length < 16) return this._list.shift();
			const temp = this._listReversed;
			this._listReversed = this._list;
			this._listReversed.reverse();
			this._list = temp;
		}
		return this._listReversed.pop();
	}

	/**
	 * Finds and removes an item
	 * @param {T} item the item
	 * @returns {void}
	 */
	delete(item) {
		const i = this._list.indexOf(item);
		if (i >= 0) {
			this._list.splice(i, 1);
		} else {
			const i = this._listReversed.indexOf(item);
			if (i >= 0) this._listReversed.splice(i, 1);
		}
	}

	[Symbol.iterator]() {
		let i = -1;
		let reversed = false;
		return {
			next: () => {
				if (!reversed) {
					i++;
					if (i < this._list.length) {
						return {
							done: false,
							value: this._list[i]
						};
					}
					reversed = true;
					i = this._listReversed.length;
				}
				i--;
				if (i < 0) {
					return {
						done: true,
						value: undefined
					};
				}
				return {
					done: false,
					value: this._listReversed[i]
				};
			}
		};
	}
}

function intersection(s1, s2) {
	var s = new Set();
	for (let e of s1) {
		if (s2.has(e)) {
			s.add(e);
		}
	}
	return s;
}


HTMLElement.prototype.getScrollTop = function() {
	var scrollTop = 0;

	var current = this;
	while (current !== null) {
		scrollTop += current.scrollTop;
		current = current.parentElement;
	}

	return scrollTop;
};

HTMLElement.prototype.getScrollLeft = function() {
	var scrollLeft = 0;

	var current = this;
	while (current !== null) {
		scrollLeft += current.scrollLeft;
		current = current.parentElement;
	}

	return scrollLeft;
}

