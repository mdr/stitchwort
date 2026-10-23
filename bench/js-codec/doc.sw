-- A neutral benchmark for the JS boundary codec (bench/js-codec/bench.mjs): a
-- document of about an hour of transcribed speech, passed in and out of
-- exported functions. Most of the cost is the generated decoder and encoder,
-- and checked-number (`SafeNat`, `SafeInt`) conversions.

import Std (List, Map, Option, SafeInt, SafeNat, Text)

type Word = { text: Text, start: SafeInt, length: SafeNat }

type Segment = { id: Text, start: SafeInt, length: SafeNat }

@[js.enum]
type Kind =
  | @[js.name "plain"] Plain
  | @[js.name "todo"] Todo
  | @[js.name "quote"] Quote

type Note = { id: Text, kind: Kind, body: Text, at: Option SafeInt }

@[js.tag "type"]
type Status =
  | @[js.name "draft"] Draft
  | @[js.name "final"] Final (reviewer: Text) (revision: SafeNat)

type Meta = { speaker: Text, language: Text, revision: SafeNat, summary: Option Text }

type Doc = { title: Text, meta: Meta, status: Status, words: List Word, segments: List Segment, notes: List Note, tags: Map Text Text, parent: Option Text }

-- Decode and encode only: the body does nothing.
export def roundTrip (d: Doc): Doc := d

-- A merge-like copy: the second version's data, with the first's title and
-- notes added to it.
export def merge (a: Doc) (b: Doc): Doc := { b | title = a.title, notes = a.notes ++ b.notes }
