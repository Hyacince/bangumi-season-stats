// ==UserScript==
// @name         Bangumi 季度番剧统计
// @namespace    bgm-season-stats
// @version      1.3.1
// @description  统计 Bangumi 用户“看过/在看”收藏中 TV 动画的季度分布（依据条目标签中的 “xxxx年x月”，如 2025年1月；特殊开播月份归入所属季度：1-3月→1月季、4-6月→4月季、7-9月→7月季、10-12月→10月季），以柱状图直观展示每个季度看了多少部动画。入口为个人主页“加入”日期所在行的蓝色胶囊“季度番剧统计 + 启动”，点击后自动填入当前主页用户名，仅本用户主页显示。
// @author       dsh
// @match        *://bgm.tv/*
// @match        *://bangumi.tv/*
// @match        *://chii.in/*
// @updateURL    https://raw.githubusercontent.com/Hyacince/bangumi-season-stats/main/bangumi-season-stats.user.js
// @downloadURL  https://raw.githubusercontent.com/Hyacince/bangumi-season-stats/main/bangumi-season-stats.user.js
// @grant        GM_xmlhttpRequest
// @connect      api.bgm.tv
// @run-at       document-end
// @noframes
// ==/UserScript==

(function () {
  'use strict';

  // ---------------------------------------------------------------------------
  // 常量
  // ---------------------------------------------------------------------------
  var VERSION = '1.3.1';
  var UA = (typeof navigator !== 'undefined' && navigator.userAgent) || 'Mozilla/5.0';
  // 季度标签：仅匹配 "xxxx年x月"（例如 2025年1月、2026年7月）
  var SEASON_RE = /^(\d{4})\s*年\s*(\d{1,2})\s*月$/;
  // 只统计 TV 动画。WEB / 剧场版 / OVA / 其它一律不统计。
  var INCLUDE_PLAT = { tv: 1 };
  var LS_SETTINGS = 'bgmSeasonStats.settings';
  var LS_CACHE = 'bgmSeasonStats.cache.v2';
  var CACHE_TTL = 7 * 24 * 3600 * 1000; // 条目详情本地缓存 7 天
  var MAX_LIST_PAGES = 300; // 每种收藏状态最多翻页数（安全上限）
  var MAX_DETAIL_RETRY = 4;

  var DEFAULT_USER = 'ashion';

  // ---------------------------------------------------------------------------
  // 运行状态
  // ---------------------------------------------------------------------------
  var state = {
    running: false,
    stopped: false,
    // 类型参数 -> 该类型下的条目 id 集合
    lists: { collect: null, do: null },
    // 已完成的条目详情缓存（本次会话内存 + localStorage 双层）
    memoryCache: {},   // id -> { subject, season, skip, ts }
    // 收集到的全部条目详情（本次运行）
    details: {},       // id -> detail
    // 计数
    processed: 0,
    pending: 0,
    failed: 0,
    skips: { web: 0, movie: 0, ova: 0, other: 0, noseason: 0, apiError: 0, unfetched: 0 },
    failStats: {},    // 失败原因 -> 数量，如 { "HTTP 404": 12, "timeout": 3 }
    failedList: [],   // [{id, reason}]
    seasonMap: {}      // "2025-1" -> { year, month, count, items: [] }
  };

  var settings = loadSettings();
  var dom = {}; // 面板 DOM 引用
  var seasonOrder = []; // 渲染用：排序后的季度 key 列表
  var userEdited = false; // 用户是否手动修改过用户名（修改后不再被自动填入覆盖）

  function loadSettings() {
    var d = {};
    try { d = JSON.parse(localStorage.getItem(LS_SETTINGS)) || {}; } catch (e) { /* ignore */ }
    return {
      user: typeof d.user === 'string' && d.user ? d.user : DEFAULT_USER,
      delay: typeof d.delay === 'number' ? d.delay : 1100,
      types: Array.isArray(d.types) ? d.types.filter(function (t) { return t === 'collect' || t === 'do'; }) : ['collect', 'do'],
      token: typeof d.token === 'string' ? d.token : ''
    };
  }
  function saveSettings() {
    try { localStorage.setItem(LS_SETTINGS, JSON.stringify(settings)); } catch (e) { /* ignore */ }
  }

  // ---------------------------------------------------------------------------
  // 小工具
  // ---------------------------------------------------------------------------
  function sleep(ms) {
    return new Promise(function (resolve) {
      var t0 = Date.now();
      (function tick() {
        if (state.stopped || Date.now() - t0 >= ms) { resolve(); return; }
        setTimeout(tick, 60);
      })();
    });
  }

  function esc(s) {
    return String(s == null ? '' : s)
      .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
  }

  function pad(n, w) {
    n = String(n);
    while (n.length < (w || 2)) n = '0' + n;
    return n;
  }

  // 特殊开播月份 → 所属季度起始月（1-3→1，4-6→4，7-9→7，10-12→10）
  function quarterOfMonth(month) {
    if (month <= 3) return 1;
    if (month <= 6) return 4;
    if (month <= 9) return 7;
    return 10;
  }

  function quarterLabel(month) {
    switch (month) {
      case 1: return '冬';
      case 4: return '春';
      case 7: return '夏';
      case 10: return '秋';
      default: return '';
    }
  }

  function quarterColor(month) {
    switch (month) {
      case 1: return '#4f9fd8'; // 冬
      case 4: return '#58b368'; // 春
      case 7: return '#f2a33c'; // 夏
      case 10: return '#e35d5d'; // 秋
      default: return '#9aa7b3';
    }
  }

  // ---------------------------------------------------------------------------
  // HTTP
  // ---------------------------------------------------------------------------
  function gmGet(url) {
    return new Promise(function (resolve, reject) {
      var headers = {
        'User-Agent': UA,
        'Accept': 'application/json'
      };
      if (settings.token) headers.Authorization = 'Bearer ' + settings.token.trim();
      var gmx = (typeof GM_xmlhttpRequest !== 'undefined') ? GM_xmlhttpRequest : null;
      if (gmx) {
        gmx({
          method: 'GET',
          url: url,
          headers: headers,
          timeout: 30000,
          onload: function (r) { resolve(r); },
          onerror: function () { reject(new Error('network')); },
          ontimeout: function () { reject(new Error('timeout')); }
        });
      } else {
        // 无 GM 环境时的兜底（浏览器直接 fetch，可能受跨域限制）
        fetch(url, { headers: headers })
          .then(function (resp) { return resp.text().then(function (t) { resolve({ status: resp.status, responseText: t }); }); })
          .catch(function (e) { reject(e); });
      }
    });
  }

  // 同源抓取 HTML（收藏列表页）。lastFetchedUrl 记录最终地址，用于检测跳转（对方收藏不可见等）
  var lastFetchedUrl = '';
  async function httpHtml(url) {
    var lastErr = null;
    for (var i = 0; i < 3; i++) {
      if (state.stopped) return '';
      try {
        var resp = await fetch(url, { credentials: 'same-origin' });
        lastFetchedUrl = resp.url || url;
        if (resp.status === 429) {
          await sleep(2500);
          continue;
        }
        if (resp.status === 404) return '';
        if (!resp.ok) { lastErr = new Error('HTTP ' + resp.status); continue; }
        return await resp.text();
      } catch (e) { lastErr = e; }
      await sleep(600 * (i + 1));
    }
    if (lastErr) throw lastErr;
    return '';
  }

  // 从收藏列表地址中取出用户名（用于跳转校验）
  function userFromListUrl(u) {
    var m = /\/anime\/list\/([^\/?#]+)/.exec(u || '');
    if (!m) return null;
    try { return decodeURIComponent(m[1]); } catch (e) { return m[1]; }
  }

  // ---------------------------------------------------------------------------
  // 解析收藏列表页，提取条目 id
  // ---------------------------------------------------------------------------
  function extractSubjectIds(html) {
    var ids = [];
    try {
      var doc = new DOMParser().parseFromString(html, 'text/html');
      var links = doc.querySelectorAll('a[href]');
      var hit = false;
      links.forEach(function (a) {
        var m = /^\/subject\/(\d+)(?:\/|$)/.exec((a.getAttribute('href') || '').trim());
        if (!m) return;
        // 收藏列表项常见形态：<li id="item_123"> 或 class 含 "item"
        var li = a.closest('li');
        var ok = false;
        if (li) {
          if (/^item_\d+$/.test(li.id || '')) ok = true;
          else if (String(li.className || '').indexOf('item') !== -1) ok = true;
        }
        if (!ok && (a.closest('#memberUserList') || a.closest('.itemList') || a.closest('.collectionList') || a.closest('#anime_collect'))) ok = true;
        if (!ok && a.className && String(a.className).indexOf('cover') !== -1) ok = true;
        if (ok) {
          hit = true;
          ids.push(parseInt(m[1], 10));
        }
      });
      if (hit) return ids;
    } catch (e) { /* fall through */ }
    // 兜底：直接正则全页抓取
    var re = /href="\/subject\/(\d+)(?:\/|")/g;
    var mm;
    while ((mm = re.exec(html)) !== null) {
      ids.push(parseInt(mm[1], 10));
    }
    return ids;
  }

  // ---------------------------------------------------------------------------
  // 解析收藏列表页：识别“看过/在看”页签的真实链接格式与标注数量
  // ---------------------------------------------------------------------------
  var TYPE_LABELS = { collect: '看过', do: '在看' };

  function parseTabInfo(html) {
    var out = { collect: null, do: null, counts: { collect: null, do: null } };
    var doc = null;
    try { doc = new DOMParser().parseFromString(html, 'text/html'); } catch (e) { doc = null; }
    if (!doc) return out;
    doc.querySelectorAll('a[href]').forEach(function (a) {
      var href = (a.getAttribute('href') || '').trim();
      // 接受完整路径式链接（/anime/list/...）与纯查询式链接（?type=collect 等）
      if (href.indexOf('anime/list') === -1 && href.charAt(0) !== '?') return;
      var text = (a.textContent || '').replace(/\s+/g, '');
      Object.keys(TYPE_LABELS).forEach(function (key) {
        if (out[key]) return;
        var label = TYPE_LABELS[key];
        if (text.indexOf(label) === -1) return;
        out[key] = href;
        var m = new RegExp(label + '[\\(（]?(\\d+)').exec(text);
        if (m) out.counts[key] = parseInt(m[1], 10);
      });
    });
    return out;
  }

  // 以 base 为基准解析相对链接
  function absUrlAgainst(href, base) {
    var a = document.createElement('a');
    a.href = base;
    a.href = href;
    return a.href;
  }

  // 去掉已有 page 参数后追加新页码
  function buildPageUrl(base, page) {
    var u = base.replace(/([?&])page=\d+/g, '$1');
    u = u.replace(/[?&]$/, '');
    return u + (u.indexOf('?') === -1 ? '?' : '&') + 'page=' + page;
  }

  // 发现每种收藏状态可用的列表 URL。
  // 优先级：页面“看过/在看”页签的真实链接 → 路径式 /anime/list/{user}/collect → 查询式 ?type=collect
  async function discoverListConfig(user) {
    var cfg = { collect: { bases: [], expected: null }, do: { bases: [], expected: null } };
    var qb = location.origin + '/anime/list/' + encodeURIComponent(user);
    var html = '';
    try { html = await httpHtml(qb); } catch (e) { html = ''; }
    var tabs = html ? parseTabInfo(html) : { collect: null, do: null, counts: {} };
    Object.keys(TYPE_LABELS).forEach(function (key) {
      var bases = [];
      if (tabs[key]) bases.push(absUrlAgainst(tabs[key], qb));
      bases.push(qb + '/' + key);
      bases.push(qb + '?type=' + key);
      var seen = {};
      cfg[key].bases = bases.filter(function (b) {
        if (seen[b]) return false;
        seen[b] = true;
        return true;
      });
      cfg[key].expected = (tabs && tabs.counts) ? tabs.counts[key] : null;
    });
    return cfg;
  }

  // 抓取某一状态的完整条目 id 列表（带翻页，兼容多种 URL 格式）
  // 返回 { ids, expected, redirectedTo }；redirectedTo 非空表示页面被跳转到别的用户（避免误统计）
  async function fetchListIds(user, cfg, key) {
    var list = [];
    var seen = {};
    var bases = (cfg && cfg[key] && cfg[key].bases) || [];
    var pageDelay = 400;
    var redirectedTo = null;
    var wantUser = String(user || '').toLowerCase();
    for (var b = 0; b < bases.length; b++) {
      if (state.stopped) break;
      var page = 1;
      while (page <= MAX_LIST_PAGES) {
        if (state.stopped) break;
        var url = buildPageUrl(bases[b], page);
        var html = '';
        try { html = await httpHtml(url); } catch (e) { html = ''; }
        if (!html) break;
        // 校验：请求的是 user 的收藏，若被站点跳转到别的用户页面则放弃该 URL 格式
        var gotUser = userFromListUrl(lastFetchedUrl);
        if (gotUser && gotUser.toLowerCase() !== wantUser) {
          redirectedTo = gotUser;
          break;
        }
        var found = extractSubjectIds(html);
        var added = 0;
        for (var i = 0; i < found.length; i++) {
          if (!seen[found[i]]) {
            seen[found[i]] = true;
            list.push(found[i]);
            added++;
          }
        }
        if (found.length === 0 || added === 0) break; // 翻到尽头 / 整页重复 / URL 格式无效
        page++;
        await sleep(pageDelay);
      }
      if (list.length || redirectedTo) break; // 取到条目 / 已确认跳转，都不再尝试其它格式
    }
    return { ids: list, expected: (cfg && cfg[key]) ? cfg[key].expected : null, redirectedTo: redirectedTo };
  }

  // ---------------------------------------------------------------------------
  // 条目详情（api.bgm.tv/v0/subjects/{id}，公开接口，无需 token）
  // ---------------------------------------------------------------------------
  async function fetchSubjectDetail(id) {
    var url = 'https://api.bgm.tv/v0/subjects/' + id;
    var lastErr = null;
    for (var attempt = 1; attempt <= MAX_DETAIL_RETRY; attempt++) {
      if (state.stopped) throw { stopped: true };
      try {
        var r = await gmGet(url);
        if (r.status === 200) {
          return JSON.parse(r.responseText);
        }
        var err = new Error('HTTP ' + r.status);
        err.status = r.status;
        if (r.status === 429 || r.status >= 500) {
          // 限流/服务端错误：退避后重试
          await sleep(r.status === 429 ? 2000 * attempt : 1500 * attempt);
          lastErr = err;
        } else {
          // 4xx（403/404 等，如 R18 受限、条目被删除）：确定性错误，不重试
          throw err;
        }
      } catch (e) {
        if (e && e.stopped) throw e;
        if (e && e.status && e.status < 500 && e.status !== 429) throw e;
        lastErr = e;
      }
      await sleep(1200 * attempt);
    }
    throw lastErr || new Error('fetch failed');
  }

  // 分析一条目：判定平台类型 + 季度标签
  function analyzeSubject(json) {
    var out = { skip: null, subject: null, season: null };
    if (!json || json.type !== 2) { // 非动画
      out.skip = 'other';
      return out;
    }
    var platform = String(json.platform || '').toLowerCase().replace(/\s+/g, '');
    if (!INCLUDE_PLAT[platform]) {
      if (platform.indexOf('web') !== -1) {
        out.skip = 'web';
      } else if (platform.indexOf('剧场版') !== -1 || platform.indexOf('movie') !== -1 || platform.indexOf('电影') !== -1) {
        out.skip = 'movie';
      } else if (platform.indexOf('ova') !== -1 || platform.indexOf('oad') !== -1) {
        out.skip = 'ova';
      } else {
        out.skip = 'other';
      }
      return out;
    }
    // 平台为 TV：寻找季度标签 "xxxx年x月"，特殊月份归入所属季度（1/4/7/10月）
    var season = null;
    var tags = Array.isArray(json.tags) ? json.tags : [];
    for (var i = 0; i < tags.length; i++) {
      var m = SEASON_RE.exec(String(tags[i].name || '').trim());
      if (m) {
        season = { year: parseInt(m[1], 10), month: quarterOfMonth(parseInt(m[2], 10)) };
        break;
      }
    }
    if (!season) {
      out.skip = 'noseason';
      return out;
    }
    out.subject = {
      id: json.id,
      name: json.name || '',
      nameCn: json.name_cn || '',
      platform: String(json.platform || ''),
      date: json.date || '',
      type: json.type
    };
    out.season = season;
    return out;
  }

  // 读取本地缓存（顺带清理过期项：普通结果 7 天，API 失败 2 小时后允许重试）
  function loadDiskCache() {
    try {
      var raw = localStorage.getItem(LS_CACHE);
      if (!raw) return {};
      var o = JSON.parse(raw) || {};
      var now = Date.now();
      var pruned = false;
      Object.keys(o).forEach(function (id) {
        var v = o[id];
        if (!v || !v.ts) { pruned = true; delete o[id]; return; }
        var ttl = v.skip === 'apiError' ? 2 * 3600 * 1000 : CACHE_TTL;
        if (now - v.ts > ttl) { pruned = true; delete o[id]; }
      });
      if (pruned) {
        try { localStorage.setItem(LS_CACHE, JSON.stringify(o)); } catch (e) { /* ignore */ }
      }
      return o;
    } catch (e) { /* ignore */ }
    return {};
  }

  // 该缓存条目是否可直接复用（API 失败的条目永远重新抓取）
  function cacheUsable(c) {
    if (!c) return false;
    if (c.skip === 'apiError') return false;
    if (c.subject && c.season) return true;
    if (c.skip) return true; // 已判定的跳过结果（剧场版/OVA/无标签等）
    return false;
  }

  // ---------------------------------------------------------------------------
  // 主流程
  // ---------------------------------------------------------------------------
  async function startRun() {
    if (state.running) return;
    var user = (dom.userInput.value || '').trim();
    if (!user) {
      // 兜底：直接用当前个人主页的用户名
      var pu = currentProfileUser();
      if (pu) {
        user = pu;
        dom.userInput.value = pu;
      }
    }
    if (!user) {
      setLog('请输入 Bangumi 用户名', 'error');
      dom.userInput.focus();
      return;
    }
    settings.user = user;
    state.runUser = user;
    settings.delay = Math.max(200, parseInt(dom.delayInput.value, 10) || 1100);
    settings.token = (dom.tokenInput ? dom.tokenInput.value : '').trim();
    settings.types = [];
    if (dom.chkCollect.checked) settings.types.push('collect');
    if (dom.chkDo.checked) settings.types.push('do');
    if (!settings.types.length) {
      setLog('请至少勾选一种收藏状态（看过 / 在看）', 'error');
      return;
    }
    saveSettings();

    state.running = true;
    state.stopped = false;
    state.lists = {};
    state.details = {};
    state.processed = 0;
    state.pending = 0;
    state.failed = 0;
    state.failStats = {};
    state.failedList = [];
    state.skips = { web: 0, movie: 0, ova: 0, other: 0, noseason: 0, apiError: 0, unfetched: 0 };
    dom.btnStart.disabled = true;
    dom.btnStop.disabled = false;
    showProgress(true);
    showResults(false);
    setLog('开始统计…（统计对象：' + user + '）');

    var diskCache = loadDiskCache();
    var memCache = state.memoryCache;

    try {
      // 1) 从收藏列表页识别“看过/在看”页签的真实链接（自动兼容路径式/查询式两种格式）
      setLog('正在读取收藏列表页…');
      var cfg = await discoverListConfig(user);

      // 2) 抓取各状态下的条目 id
      var statusOf = {}; // id -> {collect:bool, do:bool}
      var unionSet = {};
      var redirectWarn = null;
      for (var ti = 0; ti < settings.types.length; ti++) {
        var t = settings.types[ti];
        var label = t === 'collect' ? '看过' : '在看';
        setLog('正在读取「' + label + '」列表…（统计对象：' + user + '）');
        var res = await fetchListIds(user, cfg, t);
        if (res.redirectedTo) {
          redirectWarn = res.redirectedTo;
          continue; // 该状态页面被跳转到其他用户，跳过
        }
        var ids = res.ids;
        state.lists[t] = ids;
        for (var i = 0; i < ids.length; i++) {
          var id = ids[i];
          if (!statusOf[id]) statusOf[id] = {};
          statusOf[id][t] = true;
          unionSet[id] = true;
        }
        if (res.expected && ids.length && Math.abs(ids.length - res.expected) > Math.max(5, Math.round(res.expected * 0.1))) {
          setLog('警告：「' + label + '」抓到 ' + ids.length + ' 条，与页面标注的 ' + res.expected +
            ' 条差异较大，可能存在漏抓（可截图反馈以排查）。', 'warn');
        } else {
          setLog('「' + label + '」共 ' + ids.length + ' 条' + (res.expected ? '（页面标注 ' + res.expected + ' 条）' : ''));
        }
        await sleep(300);
      }
      var union = Object.keys(unionSet).map(Number);
      if (redirectWarn) {
        setLog('无法读取「' + user + '」的收藏：页面被跳转到 ' + redirectWarn +
          '。请确认用户名拼写是否正确，或对方是否公开了动画收藏。', 'error');
        return;
      }
      if (!union.length) {
        setLog('没有找到「' + user + '」的任何条目。请检查用户名是否正确、收藏列表是否公开。', 'error');
        return;
      }

      // 3) 逐个获取条目详情（跳过有效本地缓存）
      var needFetch = [];
      union.forEach(function (id) {
        if (cacheUsable(memCache[id])) return;
        if (!memCache[id] && cacheUsable(diskCache[id])) return;
        needFetch.push(id);
      });
      state.pending = needFetch.length;
      setLog('共 ' + union.length + ' 条去重条目，其中 ' + needFetch.length + ' 条需要获取详情（约 ' +
        Math.ceil((needFetch.length * settings.delay + union.length * 300) / 60000) + ' 分钟，间隔 ' + settings.delay + 'ms）…');

      for (var k = 0; k < needFetch.length; k++) {
        if (state.stopped) break;
        var sid = needFetch[k];
        var detail = null;
        try {
          detail = analyzeSubject(await fetchSubjectDetail(sid));
        } catch (e) {
          if (e && e.stopped) break;
          detail = null; // 详情抓取失败，稍后记为 apiError
          state.failed++;
          var reason = (e && e.status) ? ('HTTP ' + e.status) : ((e && e.message) ? e.message : 'unknown');
          if (!state.failStats[reason]) state.failStats[reason] = 0;
          state.failStats[reason]++;
          state.failedList.push({ id: sid, reason: reason });
        }
        state.processed++;
        updateProgress();
        if (detail) {
          memCache[sid] = detail;
        } else {
          memCache[sid] = { skip: 'apiError', subject: null, season: null, ts: Date.now() };
        }
        if (k % 10 === 0 || k === needFetch.length - 1) flushCacheToDisk(memCache);
        await sleep(settings.delay);
      }

      // 4) 汇总统计
      if (state.stopped) {
        setLog('已停止（完成 ' + state.processed + '/' + needFetch.length + ' 条详情抓取）。未抓取部分不参与统计。', 'warn');
        if (!union.length) return;
      }
      buildStats(statusOf, diskCache, memCache);
      renderResults(union.length);
      flushCacheToDisk(memCache);
    } catch (e) {
      console.error('[BGM季度统计]', e);
      setLog('运行出错：' + (e && e.message ? e.message : String(e)), 'error');
    } finally {
      state.running = false;
      dom.btnStart.disabled = false;
      dom.btnStop.disabled = true;
      showProgress(false);
    }
  }

  // 把内存缓存写回 localStorage（含磁盘缓存合并）
  function flushCacheToDisk(memCache) {
    var disk = loadDiskCache();
    var dirty = false;
    Object.keys(memCache).forEach(function (id) {
      var v = memCache[id];
      if (v && v.ts && disk[id] && disk[id].ts >= v.ts) return;
      disk[id] = { ts: Date.now(), subject: v.subject, season: v.season, skip: v.skip };
      dirty = true;
    });
    if (dirty) {
      try { localStorage.setItem(LS_CACHE, JSON.stringify(disk)); } catch (e) { /* quota 等，忽略 */ }
    }
  }

  // 汇总：把所有可用详情 + 状态归类为季度统计
  function buildStats(statusOf, diskCache, memCache) {
    var byId = {};
    var missing = 0;
    Object.keys(statusOf).forEach(function (id) {
      var cached = memCache[id] || diskCache[id] || null;
      if (cached && cached.subject && cached.season) {
        byId[id] = { subject: cached.subject, season: cached.season, status: statusOf[id] };
      } else if (cached && cached.skip) {
        state.skips[cached.skip] = (state.skips[cached.skip] || 0) + 1;
      } else {
        missing++; // 未抓取（例如中途停止）
      }
    });
    if (missing) state.skips.unfetched = missing;

    var seasonMap = {};
    Object.keys(byId).forEach(function (id) {
      var d = byId[id];
      var key = d.season.year + '-' + d.season.month;
      if (!seasonMap[key]) {
        seasonMap[key] = { year: d.season.year, month: d.season.month, count: 0, items: [] };
      }
      var st = [];
      if (d.status.collect) st.push('看过');
      if (d.status.do) st.push('在看');
      seasonMap[key].count++;
      seasonMap[key].items.push({
        id: id,
        title: d.subject.nameCn || d.subject.name || ('#' + id),
        name: d.subject.name || '',
        platform: d.subject.platform || '',
        status: st.join(' / ') || '?',
        url: 'https://bgm.tv/subject/' + id
      });
    });

    // 排序：年升序、月升序
    var keys = Object.keys(seasonMap).sort(function (a, b) {
      var A = a.split('-'), B = b.split('-');
      return (parseInt(A[0], 10) - parseInt(B[0], 10)) || (parseInt(A[1], 10) - parseInt(B[1], 10));
    });
    seasonOrder = keys;
    state.seasonMap = seasonMap;
    state.statusOf = statusOf;
    state.itemCount = Object.keys(byId).length;
  }

  // ---------------------------------------------------------------------------
  // 渲染
  // ---------------------------------------------------------------------------
  function renderResults(totalRaw) {
    showResults(true);
    var m = state.seasonMap;
    var counted = 0;
    Object.keys(m).forEach(function (k) { counted += m[k].count; });

    var collectN = (state.lists.collect || []).length;
    var doN = (state.lists.do || []).length;
    var sk = state.skips;

    var html = '';
    html += '<div class="bgmss-summary">';
    html += '<div class="chip" style="background:#eef4ff;border-color:#c7dbff;color:#1d4ed8;"><b>统计对象：</b>' + esc(state.runUser || settings.user) + '</div>';
    html += '<div class="chip"><b>' + totalRaw + '</b>去重条目（看过 ' + collectN + ' · 在看 ' + doN + '）</div>';
    html += '<div class="chip"><b>' + counted + '</b>部计入统计（TV 且有季度标签）</div>';
    html += '<div class="chip"><b>' + Object.keys(m).length + '</b>个季度</div>';
    var skipParts = [];
    if (sk.web) skipParts.push('WEB动画 ' + sk.web);
    if (sk.movie) skipParts.push('剧场版 ' + sk.movie);
    if (sk.ova) skipParts.push('OVA/OAD ' + sk.ova);
    if (sk.other) skipParts.push('其它平台 ' + sk.other);
    if (sk.noseason) skipParts.push('无季度标签 ' + sk.noseason);
    if (sk.apiError) {
      var brk = [];
      Object.keys(state.failStats || {}).forEach(function (k) { brk.push(k + '×' + state.failStats[k]); });
      skipParts.push('API获取失败 ' + sk.apiError + (brk.length ? '（' + brk.join('，') + '）' : ''));
    }
    if (sk.unfetched) skipParts.push('未抓取(中途停止) ' + sk.unfetched);
    if (skipParts.length) {
      html += '<div class="chip warn-chip">未计入：' + skipParts.join(' · ') + '</div>';
    }
    html += '</div>';

    if (!counted) {
      html += '<p class="bgmss-empty">没有符合条件的数据。可检查：<br>· 是否只勾选了「看过/在看」<br>· 条目是否在“标签”里带“xxxx年x月”<br>· 平台类型是否为 TV（WEB/剧场版/OVA 会被排除）</p>';
    } else {
      html += renderChart(m);
      html += renderDetail(m);
    }
    html += renderFooter(collectN, doN);
    dom.results.innerHTML = html;
    bindResultsEvents();
  }

  function renderChart(m) {
    var years = [];
    var mapYear = {};
    seasonOrder.forEach(function (k) {
      var s = m[k];
      if (!mapYear[s.year]) {
        mapYear[s.year] = [];
        years.push(s.year);
      }
      mapYear[s.year].push(s);
    });

    var maxC = 1;
    seasonOrder.forEach(function (k) { if (m[k].count > maxC) maxC = m[k].count; });

    var html = '<div class="bgmss-block"><div class="bgmss-block-title">📊 各季度番剧数量柱状图 <span class="tip">（点击柱子查看该季作品）</span></div>';
    html += '<div class="bgmss-scroll"><div class="bgmss-bars">';
    for (var y = 0; y < years.length; y++) {
      var year = years[y];
      var cols = mapYear[year];
      html += '<div class="bgmss-yearblock">';
      html += '<div class="bgmss-yearlabel">' + year + ' 年</div>';
      html += '<div class="bgmss-yearbars">';
      for (var c = 0; c < cols.length; c++) {
        var s = cols[c];
        var h = Math.max(2, Math.round((s.count / maxC) * 150));
        var col = quarterColor(s.month);
        var ql = quarterLabel(s.month);
        var tipNames = s.items.slice(0, 20).map(function (it) { return it.title; }).join('、');
        var tip = s.year + '年' + s.month + '月' + (ql ? '（' + ql + '季）' : '') + '：' + s.count + ' 部\n' + tipNames + (s.items.length > 20 ? '\n…共 ' + s.items.length + ' 部' : '');
        html += '<div class="bgmss-col" data-key="' + s.year + '-' + s.month + '" title="' + esc(tip) + '">';
        html += '<div class="bgmss-count">' + s.count + '</div>';
        html += '<div class="bgmss-bar" style="height:' + h + 'px;background:' + col + '"></div>';
        html += '<div class="bgmss-xlabel">' + s.month + '月' + (ql ? '<i style="color:' + col + '">' + ql + '</i>' : '') + '</div>';
        html += '</div>';
      }
      html += '</div></div>';
    }
    html += '</div></div>';
    html += '<div class="bgmss-legend">';
    [[1, '1月 冬'], [4, '4月 春'], [7, '7月 夏'], [10, '10月 秋']].forEach(function (it) {
      html += '<span class="lg"><i style="background:' + quarterColor(it[0]) + '"></i>' + it[1] + '</span>';
    });
    html += '</div></div>';
    return html;
  }

  function renderDetail(m) {
    var opts = seasonOrder.map(function (k) {
      var s = m[k];
      return '<option value="' + k + '">' + s.year + '年' + s.month + '月（' + s.count + ' 部）</option>';
    }).join('');
    var firstKey = seasonOrder[0];
    return '<div class="bgmss-block"><div class="bgmss-block-title">📋 季度作品明细</div>' +
      '<select id="bgmss-seasonSel">' + opts + '</select>' +
      '<div id="bgmss-itemList"></div></div>';
  }

  function renderSeasonList(m, key) {
    var s = m[key];
    if (!s) return '';
    var html = '<table class="bgmss-table"><thead><tr><th>标题</th><th>原名</th><th>平台</th><th>状态</th></tr></thead><tbody>';
    s.items.slice().sort(function (a, b) { return a.title.localeCompare(b.title, 'zh'); }).forEach(function (it) {
      html += '<tr><td><a href="' + esc(it.url) + '" target="_blank" rel="noopener">' + esc(it.title) + '</a></td>' +
        '<td class="muted">' + esc(it.name) + '</td><td>' + esc(it.platform) + '</td><td>' + esc(it.status) + '</td></tr>';
    });
    html += '</tbody></table>';
    return html;
  }

  function renderFooter(collectN, doN) {
    var html = '<div class="bgmss-actions">' +
      '<button id="bgmss-export">⬇ 导出 CSV</button>' +
      '<button id="bgmss-copy">📄 复制摘要</button>';
    if (state.failedList && state.failedList.length) {
      html += '<button id="bgmss-export-fail" class="danger">⛔ 导出失败清单(' + state.failedList.length + ')</button>';
    }
    html += '<button id="bgmss-cache-clear" class="danger">🗑 清除条目缓存</button>' +
      '</div>';
    html += '<div class="bgmss-note">统计口径：仅「看过 / 在看」中的 动画(TV)，按条目“标签”里的 “xxxx年x月” 判定季度，只保留 1/4/7/10 月四季；' +
      '开播时间特殊的月份（如 2月、11月）自动归入其所属季度（1-3月→1月季、4-6月→4月季、7-9月→7月季、10-12月→10月季）。' +
      '剧场版 / OVA / WEB / 其它平台、以及没有该格式季度标签的条目不计入。数据只读，不会修改你的收藏。';
    if (state.skips.apiError) {
      html += '<br>提示：API 获取失败多为 <b>404</b>（最常见是 <b>R18 条目</b>——R18 仅注册满两个月且带认证的账号可访问，匿名请求返回 404；' +
        '也可能是被合并/删除的条目）。可在 bgm.tv/dev/app 创建“个人访问令牌”填入面板，脚本会带认证重读；用“导出失败清单”核对具体条目。';
    }
    html += '</div>';
    return html;
  }

  function bindResultsEvents() {
    var cols = document.querySelectorAll('.bgmss-col');
    cols.forEach(function (el2) {
      el2.addEventListener('click', function () {
        var k = el2.getAttribute('data-key');
        var sel = document.getElementById('bgmss-seasonSel');
        if (sel && sel.querySelector('option[value="' + k + '"]')) {
          sel.value = k;
          sel.dispatchEvent(new Event('change'));
        }
        var listEl = document.getElementById('bgmss-itemList');
        if (listEl) listEl.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
      });
    });
    var sel = document.getElementById('bgmss-seasonSel');
    if (sel) {
      var render = function () {
        var listEl = document.getElementById('bgmss-itemList');
        if (listEl) listEl.innerHTML = renderSeasonList(state.seasonMap, sel.value);
      };
      sel.addEventListener('change', render);
      render();
    }
    var exp = document.getElementById('bgmss-export');
    if (exp) exp.addEventListener('click', exportCSV);
    var expf = document.getElementById('bgmss-export-fail');
    if (expf) expf.addEventListener('click', exportFailCSV);
    var cp = document.getElementById('bgmss-copy');
    if (cp) cp.addEventListener('click', copySummary);
    var cc = document.getElementById('bgmss-cache-clear');
    if (cc) cc.addEventListener('click', function () {
      try { localStorage.removeItem(LS_CACHE); } catch (e) { /* ignore */ }
      setLog('已清除条目缓存，下次运行将重新获取详情。', 'ok');
    });
  }

  function exportCSV() {
    var rows = [];
    rows.push(['年份', '月份', '季度', '标题', '原名', '平台', '状态', '条目链接']);
    Object.keys(state.seasonMap).forEach(function (k) {
      var s = state.seasonMap[k];
      var ql = quarterLabel(s.month);
      s.items.forEach(function (it) {
        rows.push([s.year, s.month, ql, it.title, it.name, it.platform, it.status, it.url]);
      });
    });
    var csv = rows.map(function (r) {
      return r.map(function (v) {
        v = String(v == null ? '' : v);
        return '"' + v.replace(/"/g, '""') + '"';
      }).join(',');
    }).join('\r\n');
    var blob = new Blob(['\ufeff' + csv], { type: 'text/csv;charset=utf-8' });
    var a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'bangumi-season-stats.csv';
    a.click();
    setTimeout(function () { URL.revokeObjectURL(a.href); }, 5000);
  }

  // 导出获取失败的条目清单，便于人工核对（R18 / 已删除等）
  function exportFailCSV() {
    var rows = [['条目ID', '失败原因', '条目链接']];
    (state.failedList || []).forEach(function (it) {
      rows.push([it.id, it.reason, 'https://bgm.tv/subject/' + it.id]);
    });
    var csv = rows.map(function (r) {
      return r.map(function (v) {
        v = String(v == null ? '' : v);
        return '"' + v.replace(/"/g, '""') + '"';
      }).join(',');
    }).join('\r\n');
    var blob = new Blob(['\ufeff' + csv], { type: 'text/csv;charset=utf-8' });
    var a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = 'bangumi-season-stats-api-failures.csv';
    a.click();
    setTimeout(function () { URL.revokeObjectURL(a.href); }, 5000);
  }

  function copySummary() {
    var lines = ['Bangumi 季度番剧统计（TV · 依据条目季度标签）', ''];
    var total = 0;
    seasonOrder.forEach(function (k) {
      var s = state.seasonMap[k];
      total += s.count;
      var ql = quarterLabel(s.month);
      lines.push(s.year + '年' + s.month + '月' + (ql ? '（' + ql + '）' : '') + '：' + s.count + ' 部');
    });
    lines.push('');
    lines.push('合计：' + total + ' 部 / ' + seasonOrder.length + ' 个季度');
    var text = lines.join('\n');
    var ta = document.createElement('textarea');
    ta.value = text;
    document.body.appendChild(ta);
    ta.select();
    try { document.execCommand('copy'); setLog('摘要已复制到剪贴板。', 'ok'); }
    catch (e) { setLog('复制失败，请手动选择文本。', 'error'); }
    document.body.removeChild(ta);
  }

  // ---------------------------------------------------------------------------
  // 进度 / 日志
  // ---------------------------------------------------------------------------
  function showProgress(on) {
    dom.progress.style.display = on ? '' : 'none';
  }
  function showResults(on) {
    dom.results.style.display = on ? '' : 'none';
  }
  function updateProgress() {
    var pct = state.pending ? Math.min(100, Math.round((state.processed / state.pending) * 100)) : 100;
    dom.progressBar.style.width = pct + '%';
    var warn = state.failed ? '（' + state.failed + ' 条获取失败，将自动跳过）' : '';
    dom.progressText.textContent = '抓取条目详情：' + state.processed + ' / ' + state.pending + warn;
    if (state.processed % 5 === 0 || state.processed === state.pending) {
      setLog('已处理 ' + state.processed + ' / ' + state.pending + ' 条…');
    }
  }
  function setLog(msg, kind) {
    if (!dom.log) return;
    dom.log.innerHTML = '';
    var span = document.createElement('span');
    span.className = kind ? 'bgmss-' + kind : '';
    span.textContent = msg;
    dom.log.appendChild(span);
  }

  // ---------------------------------------------------------------------------
  // UI 面板与入口
  // ---------------------------------------------------------------------------

  // 从当前页面地址解析个人主页用户名（/user/{用户名}）
  function currentProfileUser() {
    var m = /^\/user\/([^\/?#]+)/.exec(location.pathname || '');
    if (!m) return null;
    try { return decodeURIComponent(m[1]); } catch (e) { return m[1]; }
  }

  // 自动把当前主页用户名填入面板（点击“启动”时调用；用户手动改过则不再覆盖）
  function applyProfileUser() {
    var u = currentProfileUser();
    if (!u) return false;
    if (!dom.userInput) return false;
    if (userEdited) return false;                       // 尊重手动输入的用户名
    if (dom.userInput.value.trim() === u) return false; // 已是当前主页用户名
    dom.userInput.value = u;
    settings.user = u;
    saveSettings();
    return true;
  }

  // 定位个人主页“加入”日期所在的元素（与 “2022-2-11 加入” 同级）
  function findJoinAnchor() {
    if (!document.body) return null;
    var walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT, null);
    var node;
    while ((node = walker.nextNode())) {
      var t = node.nodeValue || '';
      if (/\d{4}-\d{1,2}-\d{1,2}\s*加入/.test(t) ||
          /加入\s*\d{4}-\d{1,2}-\d{1,2}/.test(t) ||
          /\d{4}年\d{1,2}月\d{1,2}日\s*加入/.test(t) ||
          /加入\s*\d{4}年\d{1,2}月\d{1,2}日/.test(t)) {
        return node.parentNode;
      }
    }
    return null;
  }

  // 蓝底胶囊“季度番剧统计” + 右侧“启动”入口（参考图二样式）
  function createTriggerEntry() {
    var wrap = document.createElement('span');
    wrap.id = 'bgmSeasonStatsTrigger';
    wrap.className = 'bgmss-entry';
    var pill = document.createElement('span');
    pill.className = 'bgmss-pill';
    pill.textContent = '季度番剧统计';
    var go = document.createElement('span');
    go.className = 'bgmss-go';
    go.textContent = '启动';
    wrap.appendChild(pill);
    wrap.appendChild(go);
    return wrap;
  }

  function togglePanel(panel) {
    panel.style.display = panel.style.display === 'none' ? '' : 'none';
  }

  // 构建统计面板（点击入口后以顶部浮层弹出）
  function buildPanel() {
    var panel = document.createElement('div');
    panel.id = 'bgmSeasonStatsPanel';
    panel.style.cssText = 'display:none;position:fixed;top:72px;left:50%;transform:translateX(-50%);width:min(860px,calc(100vw - 40px));max-height:80vh;overflow:auto;z-index:2147483000;background:#fff;border:1px solid #e2e6ee;border-radius:10px;box-shadow:0 8px 30px rgba(0,0,0,.22);color:#222;font-size:13px;line-height:1.6;font-family:"PingFang SC","Microsoft YaHei",sans-serif;';
    panel.innerHTML = [
      '<div style="padding:12px 14px;border-bottom:1px solid #eee;display:flex;justify-content:space-between;align-items:center;position:sticky;top:0;background:#fff;z-index:2;">',
      '<b style="font-size:15px;">📊 Bangumi 季度番剧统计 <span style="color:#999;font-weight:normal;font-size:11px;">v' + VERSION + '</span></b>',
      '<button id="bgmss-min" style="border:1px solid #ddd;background:#fff;border-radius:6px;cursor:pointer;padding:2px 9px;font-size:13px;">收起</button>',
      '</div>',
      '<div style="padding:12px 14px;">',
      '<div style="display:flex;flex-wrap:wrap;gap:8px;align-items:center;">',
      '<label>用户名 <input id="bgmss-user" type="text" style="width:130px;padding:4px 6px;border:1px solid #ccc;border-radius:5px;"></label>',
      '<label>请求间隔 <input id="bgmss-delay" type="number" min="200" step="100" style="width:76px;padding:4px 6px;border:1px solid #ccc;border-radius:5px;"> ms</label>',
      '<label><input id="bgmss-ck-collect" type="checkbox" checked> 看过</label>',
      '<label><input id="bgmss-ck-do" type="checkbox" checked> 在看</label>',
      '<button id="bgmss-start" style="padding:6px 14px;border:none;border-radius:6px;background:#52c41a;color:#fff;cursor:pointer;font-size:13px;">▶ 开始统计</button>',
      '<button id="bgmss-stop" style="padding:6px 14px;border:none;border-radius:6px;background:#f5222d;color:#fff;cursor:pointer;font-size:13px;" disabled>⏹ 停止</button>',
      '</div>',
      '<div style="margin-top:8px;">',
      '<label style="margin-right:6px;">访问令牌</label>',
      '<input id="bgmss-token" type="password" placeholder="可选：bgm.tv/dev/app 创建，用于读取 R18 条目" style="width:280px;padding:4px 6px;border:1px solid #ccc;border-radius:5px;">',
      '<span style="color:#999;font-size:11px;margin-left:6px;">令牌仅保存在本浏览器，请求 api.bgm.tv 时附加认证</span>',
      '</div>',
      '<div id="bgmss-log" style="margin-top:8px;min-height:18px;color:#555;"></div>',
      '<div id="bgmss-progress" style="display:none;margin-top:4px;height:10px;background:#f0f0f0;border-radius:5px;overflow:hidden;">',
      '<div id="bgmss-progressBar" style="height:100%;width:0;background:#1890ff;transition:width .3s;"></div></div>',
      '<div id="bgmss-progressText" style="font-size:12px;color:#777;margin-top:3px;"></div>',
      '<div id="bgmss-results" style="margin-top:10px;display:none;"></div>',
      '<div style="margin-top:8px;color:#888;font-size:12px;border-top:1px dashed #e5e5e5;padding-top:6px;">',
      '说明：仅统计「看过/在看」收藏中类型为动画、平台为 TV，且条目“标签”含 “xxxx年x月” 格式（如 2025年1月）的条目；剧场版、OVA、WEB 等不计入。<br>',
      '只保留 1/4/7/10 月四个季度，开播时间特殊的月份按所属季度归并（1-3月→1月季、4-6月→4月季、7-9月→7月季、10-12月→10月季）。<br>',
      '列表页抓取自当前域名的 /anime/list，条目详情读取自 <a href="https://api.bgm.tv" target="_blank" rel="noopener">api.bgm.tv</a>。R18 条目仅注册满两个月且带认证的账号可访问（匿名会 404）；' +
      '如需统计请在上方填入个人访问令牌。详情有 7 天本地缓存，可重复运行。</div>',
      '</div>'
    ].join('');
    document.body.appendChild(panel);

    dom.userInput = panel.querySelector('#bgmss-user');
    dom.delayInput = panel.querySelector('#bgmss-delay');
    dom.tokenInput = panel.querySelector('#bgmss-token');
    dom.chkCollect = panel.querySelector('#bgmss-ck-collect');
    dom.chkDo = panel.querySelector('#bgmss-ck-do');
    dom.btnStart = panel.querySelector('#bgmss-start');
    dom.btnStop = panel.querySelector('#bgmss-stop');
    dom.log = panel.querySelector('#bgmss-log');
    dom.results = panel.querySelector('#bgmss-results');
    dom.progress = panel.querySelector('#bgmss-progress');
    dom.progressBar = panel.querySelector('#bgmss-progressBar');
    dom.progressText = panel.querySelector('#bgmss-progressText');

    dom.userInput.value = settings.user;
    dom.delayInput.value = settings.delay;
    if (dom.tokenInput) dom.tokenInput.value = settings.token || '';
    dom.chkCollect.checked = settings.types.indexOf('collect') !== -1;
    dom.chkDo.checked = settings.types.indexOf('do') !== -1;

    dom.btnStart.addEventListener('click', startRun);
    dom.btnStop.addEventListener('click', function () {
      state.stopped = true;
      setLog('正在停止（将在当前请求完成后停下）…', 'warn');
    });
    dom.userInput.addEventListener('input', function () { userEdited = true; });
    dom.userInput.addEventListener('change', function () {
      userEdited = true;
      settings.user = dom.userInput.value.trim() || DEFAULT_USER;
      saveSettings();
    });
    if (dom.tokenInput) {
      dom.tokenInput.addEventListener('change', function () {
        settings.token = dom.tokenInput.value.trim();
        saveSettings();
      });
    }
    panel.querySelector('#bgmss-min').addEventListener('click', function () { panel.style.display = 'none'; });
    return panel;
  }

  // 挂载入口：仅在本用户主页（“加入”日期所在行）插入蓝底胶囊 + 启动入口；
  // 其它页面不做任何注入（不出现入口按钮）。
  function mountTrigger(panel, attempt) {
    var joinEl = findJoinAnchor();
    if (joinEl) {
      var entry = createTriggerEntry();
      entry.addEventListener('click', function (ev) {
        ev.preventDefault();
        applyProfileUser(); // 点击“启动”自动填入当前主页用户名
        togglePanel(panel);
      });
      joinEl.insertAdjacentElement('afterend', entry);
      return;
    }
    // 非个人主页（或该行尚未渲染）：静默不注入；稍作重试以兼容异步渲染，仍未命中则放弃
    if (attempt < 8) {
      setTimeout(function () { mountTrigger(panel, attempt + 1); }, 400);
    }
  }

  function initUI() {
    if (document.getElementById('bgmSeasonStatsPanel')) return;
    var panel = buildPanel();
    applyProfileUser(); // 主页直接预填，无需手动输入
    mountTrigger(panel, 0);
  }

  // 注入样式
  function injectCss() {
    if (document.getElementById('bgmss-css')) return;
    var style = document.createElement('style');
    style.id = 'bgmss-css';
    style.textContent = [
      '.bgmss-col{display:flex;flex-direction:column;justify-content:flex-end;align-items:center;width:52px;height:100%;cursor:pointer;margin:0 3px;}',
      '.bgmss-col:hover .bgmss-bar{opacity:.85;filter:brightness(.92);}',
      '.bgmss-bar{border-radius:4px 4px 0 0;min-height:2px;width:38px;box-shadow:inset 0 -3px 6px rgba(0,0,0,.12);}',
      '.bgmss-count{font-size:12px;font-weight:bold;color:#333;margin-bottom:3px;}',
      '.bgmss-xlabel{font-size:11px;color:#666;margin-top:4px;white-space:nowrap;text-align:center;}',
      '.bgmss-xlabel i{font-style:normal;font-size:10px;margin-left:2px;}',
      '.bgmss-bars{display:flex;flex-direction:row;align-items:flex-start;padding:10px 6px 6px;}',
      '.bgmss-yearblock{margin-right:22px;display:flex;flex-direction:column;flex:0 0 auto;}',
      '.bgmss-yearlabel{font-weight:bold;color:#1890ff;margin-bottom:6px;font-size:13px;text-align:center;border-bottom:1px solid #e8eef7;padding-bottom:2px;}',
      '.bgmss-yearbars{display:flex;flex-direction:row;align-items:flex-end;height:232px;padding-top:6px;border-bottom:1px solid #c9d4e0;/* 固定绘图区高度，柱子统一底部对齐 */}',
      '.bgmss-scroll{overflow-x:auto;padding-bottom:6px;}',
      '.bgmss-legend{margin:4px 6px 2px;}',
      '.bgmss-legend .lg{display:inline-block;margin-right:14px;font-size:12px;color:#555;}',
      '.bgmss-legend .lg i{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:4px;}',
      '.bgmss-block{margin:12px 0;border:1px solid #eef1f6;border-radius:8px;padding:10px 12px;background:#fbfcfe;}',
      '.bgmss-block-title{font-weight:bold;margin-bottom:8px;color:#333;}',
      '.bgmss-block-title .tip{font-weight:normal;color:#999;font-size:11px;}',
      '.bgmss-summary{display:flex;flex-wrap:wrap;gap:8px;}',
      '.bgmss-summary .chip{background:#f0f7ff;border:1px solid #cfe3fb;color:#0b4d96;border-radius:14px;padding:2px 10px;font-size:12px;}',
      '.bgmss-summary .chip b{font-size:14px;margin-right:2px;}',
      '.bgmss-summary .warn-chip{background:#fff7e6;border-color:#ffd591;color:#874d00;}',
      '.bgmss-table{width:100%;border-collapse:collapse;font-size:12px;}',
      '.bgmss-table th,.bgmss-table td{border-bottom:1px solid #f0f0f0;padding:4px 6px;text-align:left;vertical-align:top;}',
      '.bgmss-table th{background:#f6f8fb;color:#555;position:sticky;top:0;}',
      '.bgmss-table .muted{color:#999;font-size:11px;}',
      '.bgmss-table a{color:#1890ff;text-decoration:none;}',
      '.bgmss-table a:hover{text-decoration:underline;}',
      '.bgmss-actions{margin-top:12px;display:flex;gap:8px;flex-wrap:wrap;}',
      '.bgmss-actions button{border:1px solid #cfd6e0;background:#fff;border-radius:6px;padding:5px 12px;cursor:pointer;font-size:12px;}',
      '.bgmss-actions button:hover{background:#f0f6ff;}',
      '.bgmss-actions .danger:hover{background:#fff1f0;border-color:#ffa39e;color:#cf1322;}',
      '.bgmss-note{margin-top:8px;color:#999;font-size:11px;}',
      '.bgmss-error{color:#cf1322;}',
      '.bgmss-warn{color:#d46b08;}',
      '.bgmss-ok{color:#389e0d;}',
      '#bgmss-results select{padding:4px 8px;border:1px solid #ccc;border-radius:5px;margin-bottom:8px;font-size:13px;max-width:100%;}',
      '#bgmss-itemList{max-height:300px;overflow:auto;}',
      '.bgmss-entry{margin-left:10px;display:inline-flex;align-items:center;cursor:pointer;vertical-align:middle;}',
      '.bgmss-entry .bgmss-pill{background:#2f6fdb;color:#fff;border-radius:999px;padding:1px 10px;font-size:12px;line-height:1.7;white-space:nowrap;}',
      '.bgmss-entry .bgmss-go{color:#2f6fdb;font-size:12px;margin-left:6px;}',
      '.bgmss-entry:hover .bgmss-pill{filter:brightness(1.08);}',
      '.bgmss-entry:hover .bgmss-go{text-decoration:underline;}',
      '.bgmss-empty{color:#888;background:#fafafa;border:1px dashed #ddd;border-radius:8px;padding:12px;line-height:1.9;}'
    ].join('\n');
    document.head.appendChild(style);
  }

  // ---------------------------------------------------------------------------
  // 启动
  // ---------------------------------------------------------------------------
  function boot() {
    injectCss();
    initUI();
  }
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
