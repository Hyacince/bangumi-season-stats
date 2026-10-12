// ==UserScript==
// @name         Bangumi 收藏多标签筛选
// @namespace    bgm-multi-tag-filter
// @version      1.2.0
// @description  在 Bangumi 收藏列表页（/anime/list/{用户}/{状态}）支持同时选择多个标签筛选，弥补官方只能按单个标签查看的限制（如 /anime/list/ashion/collect?tag=TV）。入口位于“看过的标签”等标签区标题右侧；标签按数量从高到低排序；可选标签池点击添加、已选标签池点击删除。支持「同时满足(AND)」与「任一满足(OR)」。
// @author       dsh
// @match        *://bgm.tv/anime/list/*
// @match        *://bangumi.tv/anime/list/*
// @match        *://chii.in/anime/list/*
// @grant        none
// @run-at       document-end
// @noframes
// ==/UserScript==

(function () {
  'use strict';

  // ---------------------------------------------------------------------------
  // 常量与状态
  // ---------------------------------------------------------------------------
  var MAX_PAGES = 60;          // 单个标签最多翻页数（安全上限）
  var PAGE_DELAY = 250;        // 抓取标签页时的翻页间隔（ms）
  var MAX_STORE_ITEMS = 600;   // 持久化筛选结果时最多缓存多少条目的 HTML
  var SESSION_KEY = 'bgmssMtFilter.v1';
  var ACTIVE_KEY = 'bgmssMtActive.v2';   // 当前生效的筛选（含条目 HTML，用于返回列表页后恢复）
  var PAGE_KEY = 'bgmssMtPage.v2';       // 结果分页位置（轻量，单独存）

  var S = {
    tags: [],          // [{name, count}] 标签池（数量降序由渲染时排序）
    selected: {},      // name -> true
    mode: 'and',       // 'and' | 'or'
    cache: {},         // tag -> {ids:[], nodes:{id:node}}
    result: null,      // {ids, nodes, tags, mode}
    page: 1,
    pageSize: 30,
    running: false,
    hidden: [],        // 被隐藏的原始元素
    coverSize: null,   // 原始列表封面渲染尺寸（用于克隆条目时保持一致）
    container: null,   // 结果容器
    open: false,
    dom: {}
  };

  // ---------------------------------------------------------------------------
  // 工具
  // ---------------------------------------------------------------------------
  function sleep(ms) {
    return new Promise(function (r) { setTimeout(r, ms); });
  }

  function esc(s) {
    return String(s == null ? '' : s)
      .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
  }

  function status(msg, kind) {
    if (!S.dom.status) return;
    S.dom.status.textContent = msg || '';
    S.dom.status.className = 'bgmss-mt-status' + (kind ? ' is-' + kind : '');
  }

  function sortByCountDesc(list) {
    return list.slice().sort(function (a, b) {
      var ca = (a.count == null) ? -1 : a.count;
      var cb = (b.count == null) ? -1 : b.count;
      if (cb !== ca) return cb - ca;
      return String(a.name).localeCompare(String(b.name), 'zh');
    });
  }

  // 当前页面的收藏列表信息（用户名 / 状态 / 路径）
  function getListBase() {
    var path = location.pathname.replace(/\/+$/, '');
    var m = /^\/anime\/list\/([^\/]+)(?:\/([a-z_]+))?$/.exec(path);
    if (!m) return null;
    var params = new URLSearchParams(location.search);
    return {
      user: m[1],
      type: m[2] || params.get('type') || null,
      path: path
    };
  }

  // 构造“单标签”列表地址（保留路径与其它查询参数）
  function buildTagUrl(tag, page) {
    var p = new URLSearchParams(location.search);
    p.delete('page');
    p.set('tag', tag);
    if (page > 1) p.set('page', String(page));
    return location.origin + location.pathname + '?' + p.toString();
  }

  async function fetchHtml(url) {
    var lastErr = null;
    for (var i = 0; i < 3; i++) {
      try {
        var resp = await fetch(url, { credentials: 'same-origin' });
        if (resp.status === 404) return '';
        if (resp.status === 429) { await sleep(2000); continue; }
        if (!resp.ok) { lastErr = new Error('HTTP ' + resp.status); await sleep(500 * (i + 1)); continue; }
        return await resp.text();
      } catch (e) { lastErr = e; await sleep(500 * (i + 1)); }
    }
    if (lastErr) throw lastErr;
    return '';
  }

  // ---------------------------------------------------------------------------
  // 标签列表 / 条目解析
  // ---------------------------------------------------------------------------
  // 从标签链接里解析“该标签的条目数”（兼容多种标记方式）
  function extractTagCount(a, name) {
    if (!a) return null;
    // 1) 链接内的计数元素：<span class="num">812</span>
    var numEl = a.querySelector('.num, .count, .badge, small, [class*="num"], [class*="count"]');
    if (numEl) {
      var n1 = parseInt(String(numEl.textContent || '').replace(/[^\d]/g, ''), 10);
      if (!isNaN(n1)) return n1;
    }
    // 1b) 计数在链接旁边：<a>TV</a><span class="num">812</span>
    var sib = a.nextElementSibling;
    if (sib && /(^|\s)(num|count|badge)/.test(String(sib.className || ''))) {
      var n2 = parseInt(String(sib.textContent || '').replace(/[^\d]/g, ''), 10);
      if (!isNaN(n2)) return n2;
    }
    var text = String(a.textContent || '').replace(/\s+/g, '');
    // 2) 括号数字：TV (812) / TV（812）
    var m = /[（(](\d+)[)）]/.exec(text);
    if (m) return parseInt(m[1], 10);
    // 3) 数字直接跟在标签名后：TV812
    var rest = text;
    if (name && rest.indexOf(name) === 0) rest = rest.slice(name.length);
    var m2 = /^[·、:：\s]*(\d+)$/.exec(rest);
    if (m2) return parseInt(m2[1], 10);
    // 4) 数量写在外层容器里：<span>TV 812</span>
    var p = a.parentNode;
    if (p && p.nodeType === 1 && p.querySelectorAll('a[href*="tag="]').length === 1) {
      var ptext = String(p.textContent || '').replace(/\s+/g, '');
      if (ptext.length <= (name ? name.length : 0) + 8) {
        var rest2 = ptext;
        if (name && rest2.indexOf(name) === 0) rest2 = rest2.slice(name.length);
        var m3 = /^[·、:：\s]*(\d+)$/.exec(rest2);
        if (m3) return parseInt(m3[1], 10);
      }
    }
    // 5) title 提示里的“812 部/个/条”
    var m4 = /(\d+)\s*(?:部|个|条)/.exec(a.getAttribute('title') || '');
    if (m4) return parseInt(m4[1], 10);
    return null;
  }

  // 从页面上（标签筛选区）读取该用户此收藏状态下的全部标签
  function parseTagList() {
    var map = {};
    document.querySelectorAll('a[href*="tag="]').forEach(function (a) {
      var href = a.getAttribute('href') || '';
      var m = /[?&]tag=([^&]+)/.exec(href);
      if (!m) return;
      var name = m[1].replace(/\+/g, ' ');
      try { name = decodeURIComponent(name); } catch (e) { /* 保留原样 */ }
      name = name.trim();
      if (!name) return;
      var count = extractTagCount(a, name);
      if (!map[name]) map[name] = { name: name, count: count };
      else if (map[name].count == null && count != null) map[name].count = count;
    });
    // 当前地址里的 tag 也纳入
    var cur = new URLSearchParams(location.search).get('tag');
    if (cur && !map[cur]) map[cur] = { name: cur, count: null };
    return sortByCountDesc(Object.keys(map).map(function (k) { return map[k]; }));
  }

  // 从标签页 HTML 中提取条目节点与页码
  function extractItems(html) {
    var out = { items: [], maxPage: 1 };
    var doc = null;
    try { doc = new DOMParser().parseFromString(html, 'text/html'); } catch (e) { doc = null; }
    if (!doc) return out;

    doc.querySelectorAll('li[id^="item_"]').forEach(function (li) {
      var m = /^item_(\d+)$/.exec(li.id || '');
      if (m) out.items.push({ id: m[1], node: li });
    });
    // 兜底：某些皮肤下条目 li 没有 item_ 前缀 id
    if (!out.items.length) {
      doc.querySelectorAll('ul.itemList > li, #memberUserList li').forEach(function (li) {
        var a = li.querySelector('a[href*="/subject/"]');
        var m = a ? /\/subject\/(\d+)/.exec(a.getAttribute('href') || '') : null;
        if (m) out.items.push({ id: m[1], node: li });
      });
    }

    var re = /[?&]page=(\d+)/g, mm;
    while ((mm = re.exec(html)) !== null) {
      var n = parseInt(mm[1], 10);
      if (n > out.maxPage) out.maxPage = n;
    }
    if (out.maxPage > MAX_PAGES) out.maxPage = MAX_PAGES;
    return out;
  }

  // 抓取某个标签下的全部条目（带分页；结果按会话缓存）
  async function collectTag(tag) {
    if (S.cache[tag]) return S.cache[tag];
    var ids = [], seen = {}, nodes = {};
    var page = 1, maxPage = 1;
    while (page <= maxPage && page <= MAX_PAGES) {
      var html = await fetchHtml(buildTagUrl(tag, page));
      if (!html) break;
      var res = extractItems(html);
      if (page === 1) maxPage = Math.max(1, res.maxPage);
      if (!res.items.length) break;
      res.items.forEach(function (it) {
        if (seen[it.id]) return;
        seen[it.id] = 1;
        ids.push(it.id);
        nodes[it.id] = it.node;
      });
      page++;
      if (page <= maxPage) await sleep(PAGE_DELAY);
    }
    var out = { ids: ids, nodes: nodes };
    S.cache[tag] = out;
    return out;
  }

  // ---------------------------------------------------------------------------
  // 筛选与渲染
  // ---------------------------------------------------------------------------
  async function applyFilter() {
    if (S.running) return;
    var tags = Object.keys(S.selected).filter(function (k) { return S.selected[k]; });
    if (!tags.length) { status('请先在“已选标签”里添加至少一个标签', 'warn'); return; }

    S.running = true;
    setBusy(true);
    try {
      var sets = [];
      for (var i = 0; i < tags.length; i++) {
        status('正在读取标签「' + tags[i] + '」…（' + (i + 1) + '/' + tags.length + '）');
        var got = await collectTag(tags[i]);
        sets.push(got);
        status('「' + tags[i] + '」共 ' + got.ids.length + ' 条');
        await sleep(120);
      }

      var ids = [], seen = {}, nodes = {};
      if (S.mode === 'and') {
        var idSets = sets.map(function (s) {
          var st = {};
          s.ids.forEach(function (id) { st[id] = 1; });
          return st;
        });
        sets[0].ids.forEach(function (id) {
          for (var j = 1; j < idSets.length; j++) if (!idSets[j][id]) return;
          seen[id] = 1;
          ids.push(id);
        });
      } else {
        sets.forEach(function (s) {
          s.ids.forEach(function (id) {
            if (seen[id]) return;
            seen[id] = 1;
            ids.push(id);
          });
        });
      }
      sets.forEach(function (s) {
        Object.keys(s.nodes).forEach(function (id) {
          if (!nodes[id]) nodes[id] = s.nodes[id];
        });
      });

      S.result = { ids: ids, nodes: nodes, tags: tags, mode: S.mode };
      S.page = 1;
      // 先量一下原始条目的封面尺寸，克隆后按同尺寸显示（结果列表脱离了原作用域 CSS）
      if (!S.coverSize) S.coverSize = measureCoverSize();
      hideOriginalList();
      render();
      saveActive(); // 持久化筛选结果：返回列表页 / 点排序后自动恢复
      status('筛选完成：' + ids.length + ' 条（' + tags.join(S.mode === 'and' ? ' + ' : ' / ') + '）', 'ok');
      saveSelection();
    } catch (e) {
      status('筛选出错：' + (e && e.message ? e.message : e), 'error');
    } finally {
      S.running = false;
      setBusy(false);
    }
  }

  function ensureContainer() {
    if (S.container && document.body.contains(S.container)) {
      S.container.style.display = '';
      return S.container;
    }
    var c = document.createElement('div');
    c.id = 'bgmssMultiTagResult';
    var host = originalListHost();
    if (host && host.parentNode) host.parentNode.insertBefore(c, host);
    else {
      var main = document.querySelector('#columnA, .columnA, #main, #wrapper') || document.body;
      main.insertBefore(c, main.firstChild);
    }
    S.container = c;
    return c;
  }

  function originalListHost() {
    var li = document.querySelector('li[id^="item_"]') || document.querySelector('ul.itemList > li');
    return li ? li.parentNode : null;
  }

  // 测量原列表里封面图的渲染尺寸（结果列表里显式套用，避免封面被放大）
  function measureCoverSize() {
    var li = document.querySelector('li[id^="item_"]') || document.querySelector('ul.itemList > li');
    if (!li) return null;
    var img = li.querySelector('a.cover img, .cover img, .image img, img');
    if (!img) return null;
    var r = img.getBoundingClientRect();
    if (r && r.width >= 8 && r.height >= 8) return { w: Math.round(r.width), h: Math.round(r.height) };
    return null;
  }

  function applyCoverSize(li) {
    var size = S.coverSize || { w: 80, h: 112 };
    var img = li.querySelector('a.cover img, .cover img, .image img, img');
    if (!img) return;
    img.style.width = size.w + 'px';
    img.style.height = size.h + 'px';
    img.style.maxWidth = size.w + 'px';
    img.style.maxHeight = size.h + 'px';
    img.style.objectFit = 'cover';
  }

  function hideOriginalList() {
    if (S.hidden.length) return;
    var host = originalListHost();
    if (host) S.hidden.push(host);
    ['#multipage', '.page_inner', '.pageNav', '#pageLoading', '.pageNavigator'].forEach(function (sel) {
      var el = document.querySelector(sel);
      if (el) S.hidden.push(el);
    });
    S.hidden.forEach(function (el) { el.style.display = 'none'; });
  }

  function restoreOriginalList() {
    S.hidden.forEach(function (el) { el.style.display = ''; });
    S.hidden = [];
    if (S.container) {
      S.container.style.display = 'none';
      S.container.innerHTML = '';
    }
    S.result = null;
    clearActive(); // 主动退出筛选后，返回列表页不再自动恢复
    status('已退出筛选，恢复原始列表');
  }

  function render() {
    var c = ensureContainer();
    c.innerHTML = '';
    var r = S.result;
    if (!r) return;

    var total = r.ids.length;
    var pageCount = Math.max(1, Math.ceil(total / S.pageSize));
    if (S.page > pageCount) S.page = pageCount;
    var start = (S.page - 1) * S.pageSize;
    var slice = r.ids.slice(start, start + S.pageSize);

    var info = document.createElement('div');
    info.className = 'bgmss-mt-info';
    info.innerHTML = '<b>多标签筛选</b>：共 <b>' + total + '</b> 条 · 关系：' +
      (r.mode === 'and' ? '同时满足 (AND)' : '任一满足 (OR)') + ' · 标签：' +
      r.tags.map(function (t) { return '<span class="bgmss-mt-badge">' + esc(t) + '</span>'; }).join('');
    c.appendChild(info);

    if (!total) {
      var empty = document.createElement('div');
      empty.className = 'bgmss-mt-empty';
      empty.textContent = r.mode === 'and'
        ? '没有同时带有这些标签的条目。可以试试切换成“任一满足 (OR)”。'
        : '这些标签下没有条目。';
      c.appendChild(empty);
      return;
    }

    var ul = document.createElement('ul');
    ul.className = 'itemList bgmss-mt-list';
    slice.forEach(function (id) {
      var node = r.nodes[id];
      if (!node) return;
      var clone = node.cloneNode(true);
      clone.removeAttribute('id'); // 避免与原列表（已隐藏但仍在 DOM 中）产生重复 id
      applyCoverSize(clone);
      ul.appendChild(clone);
    });
    c.appendChild(ul);

    var pager = document.createElement('div');
    pager.className = 'bgmss-mt-pager';
    var prev = document.createElement('button');
    prev.type = 'button';
    prev.textContent = '‹ 上一页';
    prev.disabled = S.page <= 1;
    prev.addEventListener('click', function () { S.page--; render(); scrollToResult(); });
    var next = document.createElement('button');
    next.type = 'button';
    next.textContent = '下一页 ›';
    next.disabled = S.page >= pageCount;
    next.addEventListener('click', function () { S.page++; render(); scrollToResult(); });
    var label = document.createElement('span');
    label.textContent = '第 ' + S.page + ' / ' + pageCount + ' 页（每页 ' + S.pageSize + ' 条）';
    pager.appendChild(prev);
    pager.appendChild(label);
    pager.appendChild(next);
    c.appendChild(pager);
    savePageState(); // 记住分页位置，返回列表页后仍停在同一页
  }

  function scrollToResult() {
    if (S.container) window.scrollTo({ top: S.container.offsetTop - 80, behavior: 'smooth' });
  }

  // ---------------------------------------------------------------------------
  // 标签池（可选 / 已选）
  // ---------------------------------------------------------------------------
  function makeChip(t, selected) {
    var chip = document.createElement('button');
    chip.type = 'button';
    chip.className = 'bgmss-mt-chip' + (selected ? ' is-sel' : '');
    chip.textContent = t.name + (t.count != null ? ' (' + t.count + ')' : '');
    return chip;
  }

  function renderPools() {
    if (!S.dom.chips || !S.dom.selected) return;
    var kw = (S.dom.search && S.dom.search.value || '').trim().toLowerCase();
    var counts = {};
    S.tags.forEach(function (t) { counts[t.name] = t.count; });

    // ---- 已选标签池（点击删除）----
    var selList = sortByCountDesc(Object.keys(S.selected).filter(function (k) { return S.selected[k]; })
      .map(function (n) { return { name: n, count: counts[n] != null ? counts[n] : null }; }));
    S.dom.selected.innerHTML = '';
    selList.forEach(function (t) {
      var chip = makeChip(t, true);
      chip.title = '点击从已选标签中移除';
      chip.addEventListener('click', function (e) {
        e.preventDefault();
        e.stopPropagation();
        delete S.selected[t.name];
        renderPools();
        saveSelection();
      });
      S.dom.selected.appendChild(chip);
    });
    if (!selList.length) {
      S.dom.selected.innerHTML = '<span class="bgmss-mt-hint">暂无已选标签，点击上方标签添加</span>';
    }
    if (S.dom.selTitle) {
      S.dom.selTitle.textContent = '已选标签（点击删除）' + (selList.length ? ' — ' + selList.length + ' 个' : '');
    }

    // ---- 可选标签池（点击添加）----
    var availList = S.tags.filter(function (t) {
      if (S.selected[t.name]) return false;
      if (kw && t.name.toLowerCase().indexOf(kw) === -1) return false;
      return true;
    });
    availList = sortByCountDesc(availList);
    S.dom.chips.innerHTML = '';
    availList.forEach(function (t) {
      var chip = makeChip(t, false);
      chip.title = '点击添加为筛选标签';
      chip.addEventListener('click', function (e) {
        e.preventDefault();
        e.stopPropagation();
        S.selected[t.name] = true;
        renderPools();
        saveSelection();
      });
      S.dom.chips.appendChild(chip);
    });
    if (!availList.length) {
      S.dom.chips.innerHTML = '<span class="bgmss-mt-hint">' +
        (S.tags.length ? '没有匹配的标签（可清空搜索框）' : '未在本页找到标签列表，可在下方手动添加') + '</span>';
    }
  }

  function addManualTags() {
    var raw = (S.dom.manual && S.dom.manual.value || '').trim();
    if (!raw) return;
    raw.split(/[,，、\s]+/).forEach(function (name) {
      name = name.trim();
      if (!name) return;
      if (!S.tags.some(function (t) { return t.name === name; })) S.tags.push({ name: name, count: null });
      S.selected[name] = true;
    });
    S.tags = sortByCountDesc(S.tags);
    S.dom.manual.value = '';
    renderPools();
    saveSelection();
  }

  function saveSelection() {
    try {
      sessionStorage.setItem(SESSION_KEY, JSON.stringify({
        selected: Object.keys(S.selected).filter(function (k) { return S.selected[k]; }),
        mode: S.mode
      }));
    } catch (e) { /* ignore */ }
  }

  function loadSelection() {
    try {
      var raw = sessionStorage.getItem(SESSION_KEY);
      if (!raw) return;
      var o = JSON.parse(raw) || {};
      if (o.mode === 'or' || o.mode === 'and') S.mode = o.mode;
      (o.selected || []).forEach(function (n) { S.selected[n] = true; });
    } catch (e) { /* ignore */ }
  }

  // ---------------------------------------------------------------------------
  // 筛选结果持久化：进入条目再返回、点击顶部排序链接，都能自动恢复筛选后的界面
  // ---------------------------------------------------------------------------
  function listKey() {
    return location.pathname.replace(/\/+$/, '');
  }

  // 除 tag/page 之外的查询参数（用于判断排序等参数是否变化）
  function searchKey() {
    try {
      var p = new URLSearchParams(location.search);
      p.delete('tag');
      p.delete('page');
      var keys = [];
      p.forEach(function (v, k) { keys.push(k + '=' + v); });
      return keys.sort().join('&');
    } catch (e) { return ''; }
  }

  function saveActive() {
    if (!S.result) return;
    var ids = S.result.ids || [];
    var items = null;
    if (ids.length <= MAX_STORE_ITEMS) {
      items = [];
      for (var i = 0; i < ids.length; i++) {
        var n = S.result.nodes[ids[i]];
        if (n) items.push({ id: ids[i], html: n.outerHTML });
      }
    }
    var payload = {
      key: listKey(),
      search: searchKey(),
      tags: S.result.tags || [],
      mode: S.result.mode || S.mode,
      ids: ids,
      items: items,
      ts: Date.now()
    };
    try {
      sessionStorage.setItem(ACTIVE_KEY, JSON.stringify(payload));
    } catch (e) {
      // 体积超限：只存 ID 列表，恢复时改为重新抓取
      try {
        payload.items = null;
        sessionStorage.setItem(ACTIVE_KEY, JSON.stringify(payload));
      } catch (e2) { /* ignore */ }
    }
  }

  function loadActive() {
    try {
      var raw = sessionStorage.getItem(ACTIVE_KEY);
      if (!raw) return null;
      var o = JSON.parse(raw) || null;
      if (!o || !o.key) return null;
      if (o.key !== listKey()) return null; // 只在同一个收藏列表页恢复
      return o;
    } catch (e) { return null; }
  }

  function clearActive() {
    try { sessionStorage.removeItem(ACTIVE_KEY); } catch (e) { /* ignore */ }
    try { sessionStorage.removeItem(PAGE_KEY); } catch (e) { /* ignore */ }
  }

  function savePageState() {
    try {
      sessionStorage.setItem(PAGE_KEY, JSON.stringify({ key: listKey(), page: S.page, pageSize: S.pageSize }));
    } catch (e) { /* ignore */ }
  }

  function loadPageState() {
    try {
      var o = JSON.parse(sessionStorage.getItem(PAGE_KEY) || 'null');
      if (o && o.key === listKey()) return o;
    } catch (e) { /* ignore */ }
    return null;
  }

  function syncModeRadios() {
    if (!S.dom.panel) return;
    S.dom.panel.querySelectorAll('input[name="bgmssMtMode"]').forEach(function (r) {
      r.checked = (r.value === S.mode);
    });
    if (S.dom.size) S.dom.size.value = String(S.pageSize);
  }

  // 恢复上次的筛选（能直接复用条目 HTML 就秒开；否则按当前排序重新抓取一次）
  async function restoreActive() {
    var o = loadActive();
    if (!o) return false;
    S.selected = {};
    (o.tags || []).forEach(function (t) { S.selected[t] = true; });
    S.mode = o.mode === 'or' ? 'or' : 'and';
    S.pageSize = o.pageSize || S.pageSize;
    var ps = loadPageState();
    S.page = (ps && ps.page) ? ps.page : 1;
    if (ps && ps.pageSize) S.pageSize = ps.pageSize;
    syncModeRadios();
    renderPools();

    if (o.items && o.items.length && o.search === searchKey()) {
      var nodes = {};
      o.items.forEach(function (it) {
        try {
          var doc = new DOMParser().parseFromString('<ul>' + it.html + '</ul>', 'text/html');
          var li = doc.querySelector('li');
          if (li) nodes[it.id] = li;
        } catch (e) { /* 单条解析失败不影响整体 */ }
      });
      if (Object.keys(nodes).length) {
        S.result = { ids: o.ids || Object.keys(nodes), nodes: nodes, tags: o.tags || [], mode: S.mode };
        if (!S.coverSize) S.coverSize = measureCoverSize();
        hideOriginalList();
        render();
        status('已恢复上次的筛选结果（' + S.result.ids.length + ' 条）｜点“退出筛选”可看原始列表', 'ok');
        return true;
      }
    }

    // 排序参数变了 / 未缓存条目内容：重新抓取一次
    status('正在恢复筛选结果（按当前排序重新读取）…');
    hideOriginalList(); // 先隐藏原始列表，避免先看到未筛选的内容
    await applyFilter();
    if (!S.result || !S.result.ids.length) restoreOriginalList(); // 恢复失败则还原原始列表
    return true;
  }

  function setBusy(on) {
    if (S.dom.apply) S.dom.apply.disabled = on;
    if (S.dom.clear) S.dom.clear.disabled = on;
    if (S.dom.trigger) S.dom.trigger.textContent = on ? '多标签筛选（读取中…）' : '🏷 多标签筛选';
  }

  // ---------------------------------------------------------------------------
  // 入口定位：放在“看过的标签”等标签区标题的右侧
  // ---------------------------------------------------------------------------
  function findTagHost() {
    var anchors = Array.prototype.slice.call(document.querySelectorAll('a[href*="tag="]'));
    if (!anchors.length) return null;
    var total = anchors.length;
    var host = anchors[0].parentNode;
    while (host && host !== document.body && host.querySelectorAll('a[href*="tag="]').length < total) {
      host = host.parentNode;
    }
    if (!host || host === document.body) host = anchors[0].parentNode;
    return { anchors: anchors, host: host };
  }

  function findTagHeading() {
    var area = findTagHost();
    if (!area || !area.host) return null;
    var scope = area.host;
    var node = scope;
    for (var depth = 0; depth < 3 && node && node !== document.body; depth++) {
      var block = node.parentNode;
      if (!block) break;
      // 同一区块内，找“短文本 + 含标签二字”的元素（如 <h2>看过的标签</h2>、<span>标签</span>）
      // 注意：不使用 <a>，避免把按钮塞进链接里
      var cands = block.querySelectorAll('h1,h2,h3,h4,h5,strong,b,span,div,p,dt,label');
      for (var i = 0; i < cands.length; i++) {
        var el = cands[i];
        if (el === scope || el.contains(scope)) continue;   // 不能是标签容器的祖先
        if (el.querySelector && el.querySelector('a[href*="tag="]')) continue;
        var t = (el.textContent || '').replace(/\s+/g, '');
        if (!t || t.length > 12) continue;
        if (t.indexOf('标签') === -1) continue;
        if (el.querySelectorAll && el.querySelectorAll('*').length > 4) continue;
        return el;
      }
      // 兄弟节点里找
      var sib = node.previousElementSibling;
      while (sib) {
        var st = (sib.textContent || '').replace(/\s+/g, '');
        if (st && st.length <= 12 && st.indexOf('标签') !== -1 &&
            !(sib.querySelector && sib.querySelector('a[href*="tag="]'))) return sib;
        sib = sib.previousElementSibling;
      }
      node = block;
    }
    return null;
  }

  function createTrigger() {
    var trig = document.createElement('button');
    trig.id = 'bgmssMtTrigger';
    trig.type = 'button';
    trig.textContent = '🏷 多标签筛选';
    trig.title = '同时按多个标签筛选（弥补官方只能单标签查看）';
    trig.addEventListener('click', function (e) {
      e.preventDefault();
      e.stopPropagation();
      togglePanel();
    });
    return trig;
  }

  function mountTrigger() {
    if (document.getElementById('bgmssMtTrigger')) return true;
    var trig = createTrigger();
    S.dom.trigger = trig;
    var heading = findTagHeading();
    if (heading) {
      heading.appendChild(trig);
      return true;
    }
    var area = findTagHost();
    if (area && area.host && area.host.parentNode) {
      area.host.parentNode.insertBefore(trig, area.host);
      return true;
    }
    return false;
  }

  function fallbackFloatingTrigger() {
    if (document.getElementById('bgmssMtTrigger')) return;
    var trig = createTrigger();
    S.dom.trigger = trig;
    trig.classList.add('is-floating');
    document.body.appendChild(trig);
    status('未找到标签区，入口已放在右上角');
  }

  // ---------------------------------------------------------------------------
  // 面板
  // ---------------------------------------------------------------------------
  function buildPanel() {
    if (document.getElementById('bgmssMtPanel')) return;
    var panel = document.createElement('div');
    panel.id = 'bgmssMtPanel';
    panel.innerHTML = [
      '<div class="bgmss-mt-head">',
      '<b>多标签筛选</b>',
      '<span class="bgmss-mt-close" id="bgmssMtClose" title="关闭">×</span>',
      '</div>',
      '<div class="bgmss-mt-row"><input id="bgmssMtSearch" type="text" placeholder="搜索标签…">',
      '<button id="bgmssMtRescan" type="button" title="重新读取本页标签列表">重新读取</button></div>',
      '<div class="bgmss-mt-pool-title">可选标签（按数量排序，点击添加）</div>',
      '<div id="bgmssMtChips" class="bgmss-mt-chips"></div>',
      '<div class="bgmss-mt-pool-title" id="bgmssMtSelTitle">已选标签（点击删除）</div>',
      '<div id="bgmssMtSelected" class="bgmss-mt-chips is-selected"></div>',
      '<div class="bgmss-mt-row bgmss-mt-manual">',
      '<input id="bgmssMtManual" type="text" placeholder="手动加标签，逗号分隔">',
      '<button id="bgmssMtAdd" type="button">添加</button>',
      '</div>',
      '<div class="bgmss-mt-row">',
      '关系：<label><input type="radio" name="bgmssMtMode" value="and"> 同时满足</label>',
      '<label><input type="radio" name="bgmssMtMode" value="or"> 任一满足</label>',
      '</div>',
      '<div class="bgmss-mt-row">',
      '<button id="bgmssMtApply" type="button" class="is-primary">应用筛选</button>',
      '<button id="bgmssMtClear" type="button">退出筛选</button>',
      '</div>',
      '<div class="bgmss-mt-row">每页 <select id="bgmssMtSize"><option value="30">30</option><option value="60">60</option><option value="120">120</option></select> 条</div>',
      '<div id="bgmssMtStatus" class="bgmss-mt-status"></div>'
    ].join('');
    document.body.appendChild(panel);

    S.dom.panel = panel;
    S.dom.search = panel.querySelector('#bgmssMtSearch');
    S.dom.chips = panel.querySelector('#bgmssMtChips');
    S.dom.selected = panel.querySelector('#bgmssMtSelected');
    S.dom.selTitle = panel.querySelector('#bgmssMtSelTitle');
    S.dom.manual = panel.querySelector('#bgmssMtManual');
    S.dom.apply = panel.querySelector('#bgmssMtApply');
    S.dom.clear = panel.querySelector('#bgmssMtClear');
    S.dom.rescan = panel.querySelector('#bgmssMtRescan');
    S.dom.size = panel.querySelector('#bgmssMtSize');
    S.dom.status = panel.querySelector('#bgmssMtStatus');

    panel.querySelector('#bgmssMtClose').addEventListener('click', closePanel);
    S.dom.search.addEventListener('input', renderPools);
    panel.querySelector('#bgmssMtAdd').addEventListener('click', addManualTags);
    S.dom.manual.addEventListener('keydown', function (e) { if (e.key === 'Enter') addManualTags(); });
    S.dom.rescan.addEventListener('click', function () {
      S.tags = parseTagList();
      renderPools();
      status('已重新读取标签：' + S.tags.length + ' 个');
    });
    panel.querySelectorAll('input[name="bgmssMtMode"]').forEach(function (radio) {
      radio.addEventListener('change', function () {
        S.mode = radio.value === 'or' ? 'or' : 'and';
        saveSelection();
      });
    });
    S.dom.size.addEventListener('change', function () {
      S.pageSize = parseInt(S.dom.size.value, 10) || 30;
      if (S.result) { S.page = 1; render(); }
    });
    S.dom.apply.addEventListener('click', applyFilter);
    S.dom.clear.addEventListener('click', restoreOriginalList);

    // 点击面板外关闭（注意：标签池重绘后，点击目标可能已脱离 DOM，此时不要当成“面板外点击”）
    document.addEventListener('click', function (e) {
      if (!S.open) return;
      var t = e.target;
      if (!t) return;
      if (t.isConnected === false) return;                       // 已被重绘移除的旧节点
      if (t.nodeType === 1 && !document.documentElement.contains(t)) return;
      if (panel.contains(t)) return;
      if (S.dom.trigger && S.dom.trigger.contains(t)) return;
      closePanel();
    });
    window.addEventListener('resize', function () { if (S.open) positionPanel(); });
    window.addEventListener('scroll', function () { if (S.open) positionPanel(); }, true);

    loadSelection();
    panel.querySelectorAll('input[name="bgmssMtMode"]').forEach(function (radio) {
      radio.checked = (radio.value === S.mode);
    });
    S.dom.size.value = String(S.pageSize);
  }

  function positionPanel() {
    var panel = S.dom.panel;
    var trig = S.dom.trigger;
    if (!panel || !trig) return;
    var r = trig.getBoundingClientRect();
    var w = panel.offsetWidth || 300;
    var left = Math.min(Math.max(8, r.left), Math.max(8, window.innerWidth - w - 12));
    var top = r.bottom + 6;
    panel.style.left = left + 'px';
    panel.style.top = top + 'px';
  }

  function togglePanel() {
    if (S.open) closePanel();
    else openPanel();
  }

  function openPanel() {
    if (!S.dom.panel) return;
    S.open = true;
    S.dom.panel.classList.add('is-open');
    positionPanel();
    if (!S.tags.length) { S.tags = parseTagList(); renderPools(); }
  }

  function closePanel() {
    if (!S.dom.panel) return;
    S.open = false;
    S.dom.panel.classList.remove('is-open');
  }

  function injectCss() {
    if (document.getElementById('bgmssMtCss')) return;
    var style = document.createElement('style');
    style.id = 'bgmssMtCss';
    style.textContent = [
      '#bgmssMtTrigger{display:inline-block;margin-left:8px;padding:1px 9px;border:1px solid #2f6fdb;background:#2f6fdb;color:#fff;border-radius:999px;cursor:pointer;font-size:12px;line-height:1.6;vertical-align:middle;font-family:"PingFang SC","Microsoft YaHei",sans-serif;}',
      '#bgmssMtTrigger:hover{filter:brightness(1.08);}',
      '#bgmssMtTrigger.is-floating{position:fixed;top:70px;right:14px;z-index:2147483000;padding:6px 12px;box-shadow:0 2px 8px rgba(0,0,0,.18);}',
      '#bgmssMtPanel{position:fixed;left:0;top:0;z-index:2147483000;display:none;width:300px;max-height:76vh;overflow:auto;background:#fff;border:1px solid #dfe5ee;border-radius:10px;box-shadow:0 8px 24px rgba(0,0,0,.18);padding:10px 12px;color:#222;font-size:12px;line-height:1.6;text-align:left;font-family:"PingFang SC","Microsoft YaHei",sans-serif;}',
      '#bgmssMtPanel.is-open{display:block;}',
      '#bgmssMtPanel .bgmss-mt-head{display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;font-size:13px;}',
      '#bgmssMtPanel .bgmss-mt-close{cursor:pointer;color:#999;font-size:16px;line-height:1;padding:0 2px;}',
      '#bgmssMtPanel .bgmss-mt-close:hover{color:#333;}',
      '#bgmssMtPanel .bgmss-mt-row{margin:6px 0;display:flex;flex-wrap:wrap;align-items:center;gap:6px;}',
      '#bgmssMtPanel input[type="text"]{flex:1;min-width:0;padding:3px 6px;border:1px solid #ccc;border-radius:5px;font-size:12px;}',
      '#bgmssMtPanel button{padding:3px 8px;border:1px solid #cfd6e0;background:#fff;border-radius:5px;cursor:pointer;font-size:12px;}',
      '#bgmssMtPanel button:hover{background:#f2f6fd;}',
      '#bgmssMtPanel button.is-primary{background:#2f6fdb;border-color:#2f6fdb;color:#fff;}',
      '#bgmssMtPanel button.is-primary:hover{filter:brightness(1.06);}',
      '#bgmssMtPanel button:disabled{opacity:.55;cursor:default;}',
      '#bgmssMtPanel .bgmss-mt-pool-title{color:#666;margin:8px 0 4px;}',
      '#bgmssMtPanel .bgmss-mt-chips{max-height:150px;overflow:auto;border:1px solid #eef1f6;border-radius:6px;padding:6px;background:#fbfcfe;line-height:2;}',
      '#bgmssMtPanel .bgmss-mt-chips.is-selected{background:#f5f9ff;border-color:#cfe3fb;}',
      '#bgmssMtPanel .bgmss-mt-chip{display:inline-block;margin:2px 4px 2px 0;padding:1px 8px;border-radius:999px;border:1px solid #d3dbe6;background:#fff;color:#333;cursor:pointer;font-size:12px;}',
      '#bgmssMtPanel .bgmss-mt-chip:hover{border-color:#2f6fdb;color:#2f6fdb;}',
      '#bgmssMtPanel .bgmss-mt-chip.is-sel{background:#2f6fdb;border-color:#2f6fdb;color:#fff;}',
      '#bgmssMtPanel .bgmss-mt-chip.is-sel:hover{background:#c0392b;border-color:#c0392b;}',
      '#bgmssMtPanel .bgmss-mt-hint{color:#999;}',
      '.bgmss-mt-status{min-height:16px;color:#666;margin-top:4px;}',
      '.bgmss-mt-status.is-ok{color:#389e0d;}',
      '.bgmss-mt-status.is-warn{color:#d46b08;}',
      '.bgmss-mt-status.is-error{color:#cf1322;}',
      '#bgmssMultiTagResult{margin:8px 0 16px;}',
      '#bgmssMultiTagResult .bgmss-mt-info{background:#f0f7ff;border:1px solid #cfe3fb;color:#0b4d96;border-radius:8px;padding:6px 10px;font-size:12px;margin-bottom:8px;line-height:1.8;}',
      '#bgmssMultiTagResult .bgmss-mt-badge{display:inline-block;margin-left:4px;padding:0 8px;border-radius:999px;background:#2f6fdb;color:#fff;font-size:11px;}',
      '#bgmssMultiTagResult .bgmss-mt-empty{color:#888;background:#fafafa;border:1px dashed #ddd;border-radius:8px;padding:14px;font-size:13px;}',
      '#bgmssMultiTagResult ul.bgmss-mt-list{list-style:none;margin:0;padding:0;}',
      '#bgmssMultiTagResult ul.bgmss-mt-list > li{position:relative;padding:8px 0;min-height:64px;border-bottom:1px solid #eef1f6;}',
      '#bgmssMultiTagResult ul.bgmss-mt-list > li::after{content:"";display:block;clear:both;}',
      '#bgmssMultiTagResult ul.bgmss-mt-list > li a{text-decoration:none;}',
      '#bgmssMultiTagResult ul.bgmss-mt-list > li .cover,',
      '#bgmssMultiTagResult ul.bgmss-mt-list > li .image{float:left;margin-right:10px;}',
      '#bgmssMultiTagResult ul.bgmss-mt-list > li img{max-width:80px;max-height:112px;width:auto;height:auto;}',
      '#bgmssMultiTagResult .bgmss-mt-pager{display:flex;align-items:center;gap:10px;justify-content:center;margin:12px 0;color:#666;font-size:12px;}',
      '#bgmssMultiTagResult .bgmss-mt-pager button{padding:4px 12px;border:1px solid #cfd6e0;background:#fff;border-radius:6px;cursor:pointer;}',
      '#bgmssMultiTagResult .bgmss-mt-pager button:disabled{opacity:.5;cursor:default;}'
    ].join('\n');
    document.head.appendChild(style);
  }

  // ---------------------------------------------------------------------------
  // 启动
  // ---------------------------------------------------------------------------
  function tagStatusHint(prefix) {
    var hasCount = S.tags.some(function (t) { return t.count != null; });
    if (!S.tags.length) return '未找到标签列表，可手动添加标签';
    return prefix + '（' + S.tags.length + ' 个）' + (hasCount ? '' : '｜未读取到标签数量，暂按名称排序');
  }

  function boot() {
    if (!getListBase()) return; // 仅在收藏列表页生效
    injectCss();
    buildPanel();
    S.tags = parseTagList();
    S.coverSize = measureCoverSize(); // 在原始列表还可见时量一次封面尺寸
    renderPools();
    mountTriggerWithRetry(0);
    // 若上次在该列表页做过筛选，返回时自动恢复筛选后的界面
    restoreActive().then(function (restored) {
      if (!restored) status(tagStatusHint('已读取标签'));
    });

    // 浏览器“后退/前进”走 bfcache 时，DOM 与状态都在；这里做一次保险检查
    window.addEventListener('pageshow', function (e) {
      if (!e.persisted) return;
      if (S.result && S.container && document.body.contains(S.container) && S.container.children.length) {
        if (!S.hidden.length) hideOriginalList();
        else S.hidden.forEach(function (el) { el.style.display = 'none'; });
        return;
      }
      restoreActive();
    });
  }

  function mountTriggerWithRetry(attempt) {
    if (mountTrigger()) {
      // 标签区可能是异步渲染的，挂上入口后若标签为空再读一次
      if (!S.tags.length) {
        S.tags = parseTagList();
        if (S.tags.length) {
          renderPools();
          status(tagStatusHint('已读取标签'));
        }
      }
      return;
    }
    if (attempt < 8) setTimeout(function () { mountTriggerWithRetry(attempt + 1); }, 400);
    else fallbackFloatingTrigger();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
})();
