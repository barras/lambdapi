require open tests.OK.Z;

constant symbol R : TYPE;
symbol var : ℤ → R;
right associative commutative symbol add:R → R → R;

sequential symbol ⇧ : ℤ → R;

rule ⇧ ($x + $y) ↪ add (⇧ $x) (⇧ $y)
with ⇧ $x ↪ var $x; // must be the last rule for ⇧

symbol T000:ℤ;
symbol T001:ℤ;
symbol T002:ℤ;
symbol T003:ℤ;
symbol T004:ℤ;
symbol T005:ℤ;
symbol T006:ℤ;
symbol T007:ℤ;
symbol T008:ℤ;
symbol T009:ℤ;

symbol T010:ℤ;
symbol T011:ℤ;
symbol T012:ℤ;
symbol T013:ℤ;
symbol T014:ℤ;
symbol T015:ℤ;
symbol T016:ℤ;
symbol T017:ℤ;
symbol T018:ℤ;
symbol T019:ℤ;

symbol T020:ℤ;
symbol T021:ℤ;
symbol T022:ℤ;
symbol T023:ℤ;
symbol T024:ℤ;
symbol T025:ℤ;
symbol T026:ℤ;
symbol T027:ℤ;
symbol T028:ℤ;
symbol T029:ℤ;

symbol T030:ℤ;
symbol T031:ℤ;
symbol T032:ℤ;
symbol T033:ℤ;
symbol T034:ℤ;
symbol T035:ℤ;
symbol T036:ℤ;
symbol T037:ℤ;
symbol T038:ℤ;
symbol T039:ℤ;

symbol T040:ℤ;
symbol T041:ℤ;
symbol T042:ℤ;
symbol T043:ℤ;
symbol T044:ℤ;
symbol T045:ℤ;
symbol T046:ℤ;
symbol T047:ℤ;
symbol T048:ℤ;
symbol T049:ℤ;

symbol T050:ℤ;
symbol T051:ℤ;
symbol T052:ℤ;
symbol T053:ℤ;
symbol T054:ℤ;
symbol T055:ℤ;
symbol T056:ℤ;
symbol T057:ℤ;
symbol T058:ℤ;
symbol T059:ℤ;

symbol T060:ℤ;
symbol T061:ℤ;
symbol T062:ℤ;
symbol T063:ℤ;
symbol T064:ℤ;
symbol T065:ℤ;
symbol T066:ℤ;
symbol T067:ℤ;
symbol T068:ℤ;
symbol T069:ℤ;

symbol T070:ℤ;
symbol T071:ℤ;
symbol T072:ℤ;
symbol T073:ℤ;
symbol T074:ℤ;
symbol T075:ℤ;
symbol T076:ℤ;
symbol T077:ℤ;
symbol T078:ℤ;
symbol T079:ℤ;

symbol T080:ℤ;
symbol T081:ℤ;
symbol T082:ℤ;
symbol T083:ℤ;
symbol T084:ℤ;
symbol T085:ℤ;
symbol T086:ℤ;
symbol T087:ℤ;
symbol T088:ℤ;
symbol T089:ℤ;

symbol T090:ℤ;
symbol T091:ℤ;
symbol T092:ℤ;
symbol T093:ℤ;
symbol T094:ℤ;
symbol T095:ℤ;
symbol T096:ℤ;
symbol T097:ℤ;
symbol T098:ℤ;
symbol T099:ℤ;

// 100
symbol T100:ℤ;
symbol T101:ℤ;
symbol T102:ℤ;
symbol T103:ℤ;
symbol T104:ℤ;
symbol T105:ℤ;
symbol T106:ℤ;
symbol T107:ℤ;
symbol T108:ℤ;
symbol T109:ℤ;

symbol T110:ℤ;
symbol T111:ℤ;
symbol T112:ℤ;
symbol T113:ℤ;
symbol T114:ℤ;
symbol T115:ℤ;
symbol T116:ℤ;
symbol T117:ℤ;
symbol T118:ℤ;
symbol T119:ℤ;

symbol T120:ℤ;
symbol T121:ℤ;
symbol T122:ℤ;
symbol T123:ℤ;
symbol T124:ℤ;
symbol T125:ℤ;
symbol T126:ℤ;
symbol T127:ℤ;
symbol T128:ℤ;
symbol T129:ℤ;

symbol T130:ℤ;
symbol T131:ℤ;
symbol T132:ℤ;
symbol T133:ℤ;
symbol T134:ℤ;
symbol T135:ℤ;
symbol T136:ℤ;
symbol T137:ℤ;
symbol T138:ℤ;
symbol T139:ℤ;

symbol T140:ℤ;
symbol T141:ℤ;
symbol T142:ℤ;
symbol T143:ℤ;
symbol T144:ℤ;
symbol T145:ℤ;
symbol T146:ℤ;
symbol T147:ℤ;
symbol T148:ℤ;
symbol T149:ℤ;

symbol T150:ℤ;
symbol T151:ℤ;
symbol T152:ℤ;
symbol T153:ℤ;
symbol T154:ℤ;
symbol T155:ℤ;
symbol T156:ℤ;
symbol T157:ℤ;
symbol T158:ℤ;
symbol T159:ℤ;

symbol T160:ℤ;
symbol T161:ℤ;
symbol T162:ℤ;
symbol T163:ℤ;
symbol T164:ℤ;
symbol T165:ℤ;
symbol T166:ℤ;
symbol T167:ℤ;
symbol T168:ℤ;
symbol T169:ℤ;

symbol T170:ℤ;
symbol T171:ℤ;
symbol T172:ℤ;
symbol T173:ℤ;
symbol T174:ℤ;
symbol T175:ℤ;
symbol T176:ℤ;
symbol T177:ℤ;
symbol T178:ℤ;
symbol T179:ℤ;

symbol T180:ℤ;
symbol T181:ℤ;
symbol T182:ℤ;
symbol T183:ℤ;
symbol T184:ℤ;
symbol T185:ℤ;
symbol T186:ℤ;
symbol T187:ℤ;
symbol T188:ℤ;
symbol T189:ℤ;

symbol T190:ℤ;
symbol T191:ℤ;
symbol T192:ℤ;
symbol T193:ℤ;
symbol T194:ℤ;
symbol T195:ℤ;
symbol T196:ℤ;
symbol T197:ℤ;
symbol T198:ℤ;
symbol T199:ℤ;

// 200

symbol T200:ℤ;
symbol T201:ℤ;
symbol T202:ℤ;
symbol T203:ℤ;
symbol T204:ℤ;
symbol T205:ℤ;
symbol T206:ℤ;
symbol T207:ℤ;
symbol T208:ℤ;
symbol T209:ℤ;

symbol T210:ℤ;
symbol T211:ℤ;
symbol T212:ℤ;
symbol T213:ℤ;
symbol T214:ℤ;
symbol T215:ℤ;
symbol T216:ℤ;
symbol T217:ℤ;
symbol T218:ℤ;
symbol T219:ℤ;

symbol T220:ℤ;
symbol T221:ℤ;
symbol T222:ℤ;
symbol T223:ℤ;
symbol T224:ℤ;
symbol T225:ℤ;
symbol T226:ℤ;
symbol T227:ℤ;
symbol T228:ℤ;
symbol T229:ℤ;

symbol T230:ℤ;
symbol T231:ℤ;
symbol T232:ℤ;
symbol T233:ℤ;
symbol T234:ℤ;
symbol T235:ℤ;
symbol T236:ℤ;
symbol T237:ℤ;
symbol T238:ℤ;
symbol T239:ℤ;

symbol T240:ℤ;
symbol T241:ℤ;
symbol T242:ℤ;
symbol T243:ℤ;
symbol T244:ℤ;
symbol T245:ℤ;
symbol T246:ℤ;
symbol T247:ℤ;
symbol T248:ℤ;
symbol T249:ℤ;

symbol T250:ℤ;
symbol T251:ℤ;
symbol T252:ℤ;
symbol T253:ℤ;
symbol T254:ℤ;
symbol T255:ℤ;
symbol T256:ℤ;
symbol T257:ℤ;
symbol T258:ℤ;
symbol T259:ℤ;

symbol T260:ℤ;
symbol T261:ℤ;
symbol T262:ℤ;
symbol T263:ℤ;
symbol T264:ℤ;
symbol T265:ℤ;
symbol T266:ℤ;
symbol T267:ℤ;
symbol T268:ℤ;
symbol T269:ℤ;

symbol T270:ℤ;
symbol T271:ℤ;
symbol T272:ℤ;
symbol T273:ℤ;
symbol T274:ℤ;
symbol T275:ℤ;
symbol T276:ℤ;
symbol T277:ℤ;
symbol T278:ℤ;
symbol T279:ℤ;

symbol T280:ℤ;
symbol T281:ℤ;
symbol T282:ℤ;
symbol T283:ℤ;
symbol T284:ℤ;
symbol T285:ℤ;
symbol T286:ℤ;
symbol T287:ℤ;
symbol T288:ℤ;
symbol T289:ℤ;

symbol T290:ℤ;
symbol T291:ℤ;
symbol T292:ℤ;
symbol T293:ℤ;
symbol T294:ℤ;
symbol T295:ℤ;
symbol T296:ℤ;
symbol T297:ℤ;
symbol T298:ℤ;
symbol T299:ℤ;

// 300

symbol T300:ℤ;
symbol T301:ℤ;
symbol T302:ℤ;
symbol T303:ℤ;
symbol T304:ℤ;
symbol T305:ℤ;
symbol T306:ℤ;
symbol T307:ℤ;
symbol T308:ℤ;
symbol T309:ℤ;

symbol T310:ℤ;
symbol T311:ℤ;
symbol T312:ℤ;
symbol T313:ℤ;
symbol T314:ℤ;
symbol T315:ℤ;
symbol T316:ℤ;
symbol T317:ℤ;
symbol T318:ℤ;
symbol T319:ℤ;

symbol T320:ℤ;
symbol T321:ℤ;
symbol T322:ℤ;
symbol T323:ℤ;
symbol T324:ℤ;
symbol T325:ℤ;
symbol T326:ℤ;
symbol T327:ℤ;
symbol T328:ℤ;
symbol T329:ℤ;

symbol T330:ℤ;
symbol T331:ℤ;
symbol T332:ℤ;
symbol T333:ℤ;
symbol T334:ℤ;
symbol T335:ℤ;
symbol T336:ℤ;
symbol T337:ℤ;
symbol T338:ℤ;
symbol T339:ℤ;

symbol T340:ℤ;
symbol T341:ℤ;
symbol T342:ℤ;
symbol T343:ℤ;
symbol T344:ℤ;
symbol T345:ℤ;
symbol T346:ℤ;
symbol T347:ℤ;
symbol T348:ℤ;
symbol T349:ℤ;

symbol T350:ℤ;
symbol T351:ℤ;
symbol T352:ℤ;
symbol T353:ℤ;
symbol T354:ℤ;
symbol T355:ℤ;
symbol T356:ℤ;
symbol T357:ℤ;
symbol T358:ℤ;
symbol T359:ℤ;

symbol T360:ℤ;
symbol T361:ℤ;
symbol T362:ℤ;
symbol T363:ℤ;
symbol T364:ℤ;
symbol T365:ℤ;
symbol T366:ℤ;
symbol T367:ℤ;
symbol T368:ℤ;
symbol T369:ℤ;

symbol T370:ℤ;
symbol T371:ℤ;
symbol T372:ℤ;
symbol T373:ℤ;
symbol T374:ℤ;
symbol T375:ℤ;
symbol T376:ℤ;
symbol T377:ℤ;
symbol T378:ℤ;
symbol T379:ℤ;

symbol T380:ℤ;
symbol T381:ℤ;
symbol T382:ℤ;
symbol T383:ℤ;
symbol T384:ℤ;
symbol T385:ℤ;
symbol T386:ℤ;
symbol T387:ℤ;
symbol T388:ℤ;
symbol T389:ℤ;

symbol T390:ℤ;
symbol T391:ℤ;
symbol T392:ℤ;
symbol T393:ℤ;
symbol T394:ℤ;
symbol T395:ℤ;
symbol T396:ℤ;
symbol T397:ℤ;
symbol T398:ℤ;
symbol T399:ℤ;

// 400

symbol T400:ℤ;
symbol T401:ℤ;
symbol T402:ℤ;
symbol T403:ℤ;
symbol T404:ℤ;
symbol T405:ℤ;
symbol T406:ℤ;
symbol T407:ℤ;
symbol T408:ℤ;
symbol T409:ℤ;

symbol T410:ℤ;
symbol T411:ℤ;
symbol T412:ℤ;
symbol T413:ℤ;
symbol T414:ℤ;
symbol T415:ℤ;
symbol T416:ℤ;
symbol T417:ℤ;
symbol T418:ℤ;
symbol T419:ℤ;

symbol T420:ℤ;
symbol T421:ℤ;
symbol T422:ℤ;
symbol T423:ℤ;
symbol T424:ℤ;
symbol T425:ℤ;
symbol T426:ℤ;
symbol T427:ℤ;
symbol T428:ℤ;
symbol T429:ℤ;

symbol T430:ℤ;
symbol T431:ℤ;
symbol T432:ℤ;
symbol T433:ℤ;
symbol T434:ℤ;
symbol T435:ℤ;
symbol T436:ℤ;
symbol T437:ℤ;
symbol T438:ℤ;
symbol T439:ℤ;

symbol T440:ℤ;
symbol T441:ℤ;
symbol T442:ℤ;
symbol T443:ℤ;
symbol T444:ℤ;
symbol T445:ℤ;
symbol T446:ℤ;
symbol T447:ℤ;
symbol T448:ℤ;
symbol T449:ℤ;

symbol T450:ℤ;
symbol T451:ℤ;
symbol T452:ℤ;
symbol T453:ℤ;
symbol T454:ℤ;
symbol T455:ℤ;
symbol T456:ℤ;
symbol T457:ℤ;
symbol T458:ℤ;
symbol T459:ℤ;

symbol T460:ℤ;
symbol T461:ℤ;
symbol T462:ℤ;
symbol T463:ℤ;
symbol T464:ℤ;
symbol T465:ℤ;
symbol T466:ℤ;
symbol T467:ℤ;
symbol T468:ℤ;
symbol T469:ℤ;

symbol T470:ℤ;
symbol T471:ℤ;
symbol T472:ℤ;
symbol T473:ℤ;
symbol T474:ℤ;
symbol T475:ℤ;
symbol T476:ℤ;
symbol T477:ℤ;
symbol T478:ℤ;
symbol T479:ℤ;

symbol T480:ℤ;
symbol T481:ℤ;
symbol T482:ℤ;
symbol T483:ℤ;
symbol T484:ℤ;
symbol T485:ℤ;
symbol T486:ℤ;
symbol T487:ℤ;
symbol T488:ℤ;
symbol T489:ℤ;

symbol T490:ℤ;
symbol T491:ℤ;
symbol T492:ℤ;
symbol T493:ℤ;
symbol T494:ℤ;
symbol T495:ℤ;
symbol T496:ℤ;
symbol T497:ℤ;
symbol T498:ℤ;
symbol T499:ℤ;

// lists

//user	0m0,11s

symbol rev2 ≔
  T001 + T000;

symbol rev5 ≔
  T004 + T003 + T002 + T001 + T000;

symbol rev10 ≔
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;

symbol rev12 ≔
  T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;

symbol rev15 ≔
  T014 + T013 + T012 + T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;

symbol rev20 ≔
  T019 + T018 + T017 + T016 + T015 + T014 + T013 + T012 + T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;

//debug +ew;
compute ⇧ rev2;
compute ⇧ rev5;
compute ⇧ rev10;
compute ⇧ rev12;
compute ⇧ rev15;
compute ⇧ rev20;
//2  ac: 1	insert: 2	perm: 1
//5  ac: 4	insert: 14	perm: 10
//10 ac: 9	insert: 54	perm: 45
//12 ac: 11	insert: 77	perm: 66
//15 ac: 14	insert: 119	perm: 105
//20 ac: 19	insert: 209	perm: 190

compute ⇧ (rev2 + rev2);
compute ⇧ (rev5 + rev5);
compute ⇧ (rev10 + rev10);
compute ⇧ (rev12 + rev12);
compute ⇧ (rev15 + rev15);
compute ⇧ (rev20 + rev20);
//ac: 3	insert: 9	perm: 3
//ac: 9	insert: 54	perm: 30
//ac: 19	insert: 209	perm: 135
//ac: 23	insert: 299	perm: 198
//ac: 29	insert: 464	perm: 315
//ac: 39	insert: 819	perm: 570
// ac: # of +
// perm: 3n(n-1)/2


// Rewrites rules AC symbol appears on rhs, the term has to be AC-normalized
// Howerver, we should be able to notice that $y is already sorted...
// this means 1 insert, constant time
rule add (var $x) (var $x) ↪ var $x
with add (var $x) (add (var $x) $y) ↪ add (var $x) $y;


compute ⇧ rev2;
compute ⇧ rev5; //slow aliens ac: 16	insert: 46	perm: 10
compute ⇧ rev10;
compute ⇧ rev12;
compute ⇧ rev15;
compute ⇧ rev20;
// added aco in whnd_stk but not tree_walk
//2  ac: 1	insert: 2	perm: 1
//5  ac: 10	insert: 30	perm: 10
//10 ac: 45	insert: 210	perm: 45
//12 ac: 66	insert: 352	perm: 66
//15 ac: 105	insert: 665	perm: 105
//20 ac: 190	insert: 1520	perm: 190
// ac=perm: n(n-1)/2


//debug +ew;
compute ⇧ (rev2 + rev2);
//tag: 5 	cut: 5	ac: 2	insert: 7	perm: 3
//compute ⇧ ((T002 + T001 + T000) + (T002 + T001 + T000)); // untag ac: 9	insert: 29	perm: 9
//tag: 15 	cut: 20	ac: 5	insert: 20	perm: 9

compute ⇧ (rev5 + rev5);
//shr: 11	tag: 0 	cut: 0	ac: 25	insert: 100	perm: 30
//tag: 93 	cut: 140	ac: 27	insert: 120	perm: 30
//tag: 309 	cut: 0  	ac: 109	insert: 418	perm: 30


compute ⇧ (rev10 + rev10);
compute ⇧ (rev12 + rev12);
compute ⇧ (rev15 + rev15);
compute ⇧ (rev20 + rev20);
//2  ac: 4	insert: 11	perm: 3
//5  ac: 25	insert: 100	perm: 30
//10 ac: 100	insert: 575	perm: 135
//12 ac: 144	insert: 926	perm: 198
//15 ac: 225	insert: 1675	perm: 315
//20 ac: 400	insert: 3650	perm: 570

// with ac whnf tag
//shr: 5	tag: 7 	cut: 1	ac: 4	insert: 11	perm: 3
//shr: 11	tag: 72 	cut: 38	ac: 23	insert: 95	perm: 30
//shr: 21	tag: 447 	cut: 328	ac: 93	insert: 540	perm: 135
//shr: 25	tag: 737 	cut: 570	ac: 135	insert: 872	perm: 198
//shr: 31	tag: 1372 	cut: 1118	ac: 213	insert: 1585	perm: 315
//shr: 41	tag: 3097 	cut: 2658	ac: 383	insert: 3480	perm: 570


/* insertion sort
+no rw, 1 side:
shr: 1	tag: 1  	cut: 0	ac: 1	insert: 2	perm: 1
shr: 1	tag: 4  	cut: 3	ac: 1	insert: 5	perm: 10
shr: 1	tag: 9  	cut: 8	ac: 1	insert: 10	perm: 45
shr: 1	tag: 11 	cut: 10	ac: 1	insert: 12	perm: 66
shr: 1	tag: 14 	cut: 13	ac: 1	insert: 15	perm: 105
shr: 1	tag: 19 	cut: 18	ac: 1	insert: 20	perm: 190

+no rw, 2 sides:
shr: 3	tag: 3  	cut: 2	ac: 1	insert: 4	perm: 3
shr: 3	tag: 9  	cut: 8	ac: 1	insert: 10	perm: 30
shr: 3	tag: 19 	cut: 18	ac: 1	insert: 20	perm: 135
shr: 3	tag: 23 	cut: 22	ac: 1	insert: 24	perm: 198
shr: 3	tag: 29 	cut: 28	ac: 1	insert: 30	perm: 315
shr: 3	tag: 39 	cut: 38	ac: 1	insert: 40	perm: 570

+rw, 1 side:
shr: 1	tag: 1  	cut: 0  	ac: 1	insert: 2	perm: 1
shr: 1	tag: 4  	cut: 9  	ac: 1	insert: 5	perm: 10
shr: 1	tag: 9  	cut: 44  	ac: 1	insert: 10	perm: 45
shr: 1	tag: 11 	cut: 65 	ac: 1	insert: 12	perm: 66
shr: 1	tag: 14 	cut: 104	ac: 1	insert: 15	perm: 105
shr: 1	tag: 19 	cut: 189	ac: 1	insert: 20	perm: 190

+rw, 2 sides:
shr: 5	tag: 4  	cut: 2  	ac: 2	insert: 6	perm: 3
shr: 11	tag: 19 	cut: 23 	ac: 5	insert: 24	perm: 30
shr: 21	tag: 64 	cut: 118	ac: 10	insert: 74	perm: 135
shr: 25	tag: 89 	cut: 177	ac: 12	insert: 101	perm: 198
shr: 31	tag: 134 	cut: 288	ac: 15	insert: 149	perm: 315
shr: 41	tag: 229 	cut: 533	ac: 20	insert: 249	perm: 570

*/
/* mixed merge sort

shr: 1	tag: 1  	cut: 0	ac: 1	insert: 1	perm: 1
shr: 1	tag: 4  	cut: 3	ac: 1	insert: 4	perm: 6
shr: 1	tag: 9  	cut: 8	ac: 1	insert: 9	perm: 17
shr: 1	tag: 11 	cut: 10	ac: 1	insert: 11	perm: 20
shr: 1	tag: 14 	cut: 13	ac: 1	insert: 14	perm: 28
shr: 1	tag: 19 	cut: 18	ac: 1	insert: 19	perm: 44

shr: 3	tag: 3  	cut: 2	ac: 1	insert: 3	perm: 5
shr: 3	tag: 9  	cut: 8	ac: 1	insert: 9	perm: 22
shr: 3	tag: 19 	cut: 18	ac: 1	insert: 19	perm: 55
shr: 3	tag: 23 	cut: 22	ac: 1	insert: 23	perm: 71
shr: 3	tag: 29 	cut: 28	ac: 1	insert: 29	perm: 93
shr: 3	tag: 39 	cut: 38	ac: 1	insert: 39	perm: 134

shr: 1	tag: 1  	cut: 0  	ac: 1	insert: 1	perm: 1
shr: 1	tag: 4  	cut: 9  	ac: 1	insert: 4	perm: 6
shr: 1	tag: 9  	cut: 44 	ac: 1	insert: 9	perm: 17
shr: 1	tag: 11 	cut: 65 	ac: 1	insert: 11	perm: 20
shr: 1	tag: 14 	cut: 104	ac: 1	insert: 14	perm: 28
shr: 1	tag: 19 	cut: 189	ac: 1	insert: 19	perm: 44

shr: 5	tag: 4  	cut: 2  	ac: 2	insert: 3	perm: 5
shr: 11	tag: 19 	cut: 23 	ac: 5	insert: 9	perm: 22
shr: 21	tag: 64 	cut: 118	ac: 10	insert: 19	perm: 55
shr: 25	tag: 89 	cut: 177	ac: 12	insert: 23	perm: 71
shr: 31	tag: 134 	cut: 288	ac: 15	insert: 29	perm: 93
shr: 41	tag: 229 	cut: 533	ac: 20	insert: 39	perm: 134

*/

symbol rev30 ≔
  T039 + T038 + T037 + T036 + T035 + T034 + T033 + T032 + T031 + T030 +
  T029 + T028 + T027 + T026 + T025 + T024 + T023 + T022 + T021 + T020 +
  T019 + T018 + T017 + T016 + T015 + T014 + T013 + T012 + T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;

//compute ⇧ rev30; //user	0m0,35s

symbol rev40 ≔
  T049 + T048 + T047 + T046 + T045 + T044 + T043 + T042 + T041 + T040 +
  T039 + T038 + T037 + T036 + T035 + T034 + T033 + T032 + T031 + T030 +
  T029 + T028 + T027 + T026 + T025 + T024 + T023 + T022 + T021 + T020 +
  T019 + T018 + T017 + T016 + T015 + T014 + T013 + T012 + T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;
//compute ⇧ rev40; //user	0m0,57s

symbol rev50 ≔
  T059 + T058 + T057 + T056 + T055 + T054 + T053 + T052 + T051 + T050 +
  T049 + T048 + T047 + T046 + T045 + T044 + T043 + T042 + T041 + T040 +
  T039 + T038 + T037 + T036 + T035 + T034 + T033 + T032 + T031 + T030 +
  T029 + T028 + T027 + T026 + T025 + T024 + T023 + T022 + T021 + T020 +
  T019 + T018 + T017 + T016 + T015 + T014 + T013 + T012 + T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;
//compute ⇧ rev50; //user	0m0,93s

symbol rev100 ≔
  T099 + T098 + T097 + T096 + T095 + T094 + T093 + T092 + T091 + T090 +
  T089 + T088 + T087 + T086 + T085 + T084 + T083 + T082 + T081 + T080 +
  T079 + T078 + T077 + T076 + T075 + T074 + T073 + T072 + T071 + T070 +
  T069 + T068 + T067 + T066 + T065 + T064 + T063 + T062 + T061 + T060 +
  T059 + T058 + T057 + T056 + T055 + T054 + T053 + T052 + T051 + T050 +
  T049 + T048 + T047 + T046 + T045 + T044 + T043 + T042 + T041 + T040 +
  T039 + T038 + T037 + T036 + T035 + T034 + T033 + T032 + T031 + T030 +
  T029 + T028 + T027 + T026 + T025 + T024 + T023 + T022 + T021 + T020 +
  T019 + T018 + T017 + T016 + T015 + T014 + T013 + T012 + T011 + T010 +
  T009 + T008 + T007 + T006 + T005 + T004 + T003 + T002 + T001 + T000;
//compute ⇧ rev100; //user	0m3.600s

symbol rev200 ≔
  T199 + T198 + T197 + T196 + T195 + T194 + T193 + T192 + T191 + T190 +
  T189 + T188 + T187 + T186 + T185 + T184 + T183 + T182 + T181 + T180 +
  T179 + T178 + T177 + T176 + T175 + T174 + T173 + T172 + T171 + T170 +
  T169 + T168 + T167 + T166 + T165 + T164 + T163 + T162 + T161 + T160 +
  T159 + T158 + T157 + T156 + T155 + T154 + T153 + T152 + T151 + T150 +
  T149 + T148 + T147 + T146 + T145 + T144 + T143 + T142 + T141 + T140 +
  T139 + T138 + T137 + T136 + T135 + T134 + T133 + T132 + T131 + T130 +
  T129 + T128 + T127 + T126 + T125 + T124 + T123 + T122 + T121 + T120 +
  T119 + T118 + T117 + T116 + T115 + T114 + T113 + T112 + T111 + T110 +
  T109 + T108 + T107 + T106 + T105 + T104 + T103 + T102 + T101 + T100 +
  rev100;
//compute ⇧ rev200; //user	0m26s
// no RW user	0m0,452s
// with rw ac: 199	insert: 20099	perm: 19900

// with RW  user	0m10,058s
//ac: 19900	insert: 1353200	perm: 19900
// +ac tagging
//shr: 101	tag: 199 	cut: 198	ac: 1	insert: 200	perm: 19900
//user	0m0,304s
// RW, tags
//user	0m0,577s
//shr: 101	tag: 199 	cut: 19899	ac: 1	insert: 200	perm: 19900

//compute ⇧ (rev200 + rev200);
//user	0m1,320s
//shr: 601	tag: 20299 	cut: 59303	ac: 200	insert: 20499	perm: 59700

symbol rev300 ≔
  T299 + T298 + T297 + T296 + T295 + T294 + T293 + T292 + T291 + T290 +
  T289 + T288 + T287 + T286 + T285 + T284 + T283 + T282 + T281 + T280 +
  T279 + T278 + T277 + T276 + T275 + T274 + T273 + T272 + T271 + T270 +
  T269 + T268 + T267 + T266 + T265 + T264 + T263 + T262 + T261 + T260 +
  T259 + T258 + T257 + T256 + T255 + T254 + T253 + T252 + T251 + T250 +
  T249 + T248 + T247 + T246 + T245 + T244 + T243 + T242 + T241 + T240 +
  T239 + T238 + T237 + T236 + T235 + T234 + T233 + T232 + T231 + T230 +
  T229 + T228 + T227 + T226 + T225 + T224 + T223 + T222 + T221 + T220 +
  T219 + T218 + T217 + T216 + T215 + T214 + T213 + T212 + T211 + T210 +
  T209 + T208 + T207 + T206 + T205 + T204 + T203 + T202 + T201 + T200 +
  rev200;
//compute ⇧ rev300; //
// no RW
//user	0m0,863s
//ac: 299	insert: 45149	perm: 44850
// no rw, tags
//user	0m0,558s
//shr: 201	tag: 299 	cut: 298	ac: 1	insert: 300	perm: 44850

symbol rev400 ≔
  T399 + T398 + T397 + T396 + T395 + T394 + T393 + T392 + T391 + T390 +
  T389 + T388 + T387 + T386 + T385 + T384 + T383 + T382 + T381 + T380 +
  T379 + T378 + T377 + T376 + T375 + T374 + T373 + T372 + T371 + T370 +
  T369 + T368 + T367 + T366 + T365 + T364 + T363 + T362 + T361 + T360 +
  T359 + T358 + T357 + T356 + T355 + T354 + T353 + T352 + T351 + T350 +
  T349 + T348 + T347 + T346 + T345 + T344 + T343 + T342 + T341 + T340 +
  T339 + T338 + T337 + T336 + T335 + T334 + T333 + T332 + T331 + T330 +
  T329 + T328 + T327 + T326 + T325 + T324 + T323 + T322 + T321 + T320 +
  T319 + T318 + T317 + T316 + T315 + T314 + T313 + T312 + T311 + T310 +
  T309 + T308 + T307 + T306 + T305 + T304 + T303 + T302 + T301 + T300 +
  rev300;
//compute ⇧ rev400; //
// no RW
//user	0m1,502s
// ac: 399	insert: 80199	perm: 79800
// no rw, tags
//user	0m0,926s
//shr: 301	tag: 399 	cut: 398	ac: 1	insert: 400	perm: 79800

symbol rev500 ≔
  T499 + T498 + T497 + T496 + T495 + T494 + T493 + T492 + T491 + T490 +
  T489 + T488 + T487 + T486 + T485 + T484 + T483 + T482 + T481 + T480 +
  T479 + T478 + T477 + T476 + T475 + T474 + T473 + T472 + T471 + T470 +
  T469 + T468 + T467 + T466 + T465 + T464 + T463 + T462 + T461 + T460 +
  T459 + T458 + T457 + T456 + T455 + T454 + T453 + T452 + T451 + T450 +
  T449 + T448 + T447 + T446 + T445 + T444 + T443 + T442 + T441 + T440 +
  T439 + T438 + T437 + T436 + T435 + T434 + T433 + T432 + T431 + T430 +
  T429 + T428 + T427 + T426 + T425 + T424 + T423 + T422 + T421 + T420 +
  T419 + T418 + T417 + T416 + T415 + T414 + T413 + T412 + T411 + T410 +
  T409 + T408 + T407 + T406 + T405 + T404 + T403 + T402 + T401 + T400 +
  rev400;
//compute ⇧ rev500; //
// no RW
// user	0m2,232s
// ac: 499	insert: 125249	perm: 124750
// no rw, tags
//user	0m1,436s
//shr: 401	tag: 499 	cut: 498	ac: 1	insert: 500	perm: 124750
// RW, tags
//user	0m3,322s
//shr: 401	tag: 499 	cut: 124749	ac: 1	insert: 500	perm: 124750

//compute ⇧ (rev500 + rev500);
//user	0m7,858s
//shr: 1801	tag: 125749 	cut: 373253	ac: 500	insert: 126249	perm: 374250

