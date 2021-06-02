"use strict";
Vue.use(httpVueLoader);
Vue.use(AsyncComputed);

Vue.component('contents', 'url:/sympy/vue/contents.vue');

var data = {
	packages: packages,
	theorems: theorems,
};

//console.log("data = " + JSON.stringify(data));

var app = new Vue({
	el: '#root',
	data: data,	
});

promise(()=>{
	document.querySelector('.theorem, .package').focus();
});			