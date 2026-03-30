import asyncio
import logging
import json
import aiohttp
import os
import random
import re
from datetime import datetime, timedelta
from telegram import (Update, InlineKeyboardButton, InlineKeyboardMarkup,
                       InputMediaPhoto, InputMediaVideo, InputMediaDocument)
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes, MessageHandler, filters
from telegram.constants import ParseMode
from telegram.error import NetworkError, TimedOut, RetryAfter
import time
import tempfile
from collections import Counter, deque
import numpy as np
import pickle
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
import hashlib
from pathlib import Path
from pymongo import MongoClient

# Pyrogram for user account (premium emoji support)
from pyrogram import Client
from pyrogram.errors import FloodWait, PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant
from pyrogram.enums import ParseMode as PyrogramParseMode
from pyrogram.types import InputMediaPhoto as PyrogramInputMediaPhoto
from pyrogram.types import InputMediaVideo as PyrogramInputMediaVideo
from pyrogram.types import InputMediaDocument as PyrogramInputMediaDocument
from pyrogram.types import InputMediaAnimation as PyrogramInputMediaAnimation

# Configure logging
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logging.getLogger('httpx').setLevel(logging.WARNING)
logging.getLogger('apscheduler').setLevel(logging.WARNING)
logging.getLogger('telegram').setLevel(logging.WARNING)
logging.getLogger('pyrogram').setLevel(logging.WARNING)


class WinGoBotEnhanced:
    """
    Advanced WinGo Prediction Bot with AI Pattern Recognition
    Features:
    - Per-channel custom prediction schedules
    - 50min prediction / 10min break cycle (configurable per channel)
    - Morning message at 5:00 AM
    - Night message at 12:00 AM (midnight)
    - Session start message 5 minutes before each session
    - AI-powered pattern recognition
    - Multi-channel support
    - Premium emoji support via Pyrogram user account
    - Custom messages with media support
    - Event media with view/delete options
    - MongoDB persistence
    """
    
    def __init__(self, bot_token, api_id=None, api_hash=None, phone=None):
        # Core bot settings
        self.bot_token = bot_token
        self.config_file = 'wingo_config.json'
        self.templates_file = 'templates.json'
        self.emoji_config_file = 'emoji_config.json'
        self.ai_model_file = 'ai_pattern_model.pkl'
        self.pattern_history_file = 'pattern_history.json'
        self.custom_messages_file = 'custom_messages.json'

        # MongoDB storage
        self.bot_name = Path(__file__).stem
        self.mongo_uri = os.getenv('MONGO_URI', 'mongodb+srv://avinash:avinash12@cluster0.wnwd1fv.mongodb.net/?appName=Cluster0')
        self.mongo_db_name = os.getenv('MONGO_DB', 'sanjay_bots')
        self.mongo_client = None
        self.mongo_db = None
        self._init_mongo()

        # Pyrogram User Account for premium emojis
        self.api_id = api_id
        self.api_hash = api_hash
        self.phone = phone
        self.user_app = None
        self.user_client_initialized = False
        self.user_client_lock = asyncio.Lock()
        self.use_user_account = bool(api_id and api_hash and phone)
        
        # Channel resolution cache
        self.username_to_id = {}
        self.id_to_username = {}
        self.resolved_channels = set()
        self.failed_channels = set()
        self.resolution_in_progress = False
        self.user_client_connected = False
        self.user_client_keepalive_task = None
        
        self.emoji_placeholders = {}

        # ============= GLOBAL SCHEDULE =============
        self.prediction_start_hour = 6      # 6:00 AM start
        self.prediction_end_hour = 24        # 12:00 AM midnight end
        self.prediction_active_minutes = 50  # 50 minutes of predictions
        self.prediction_break_minutes = 10   # 10 minutes break
        
        # Morning message at 5:00 AM
        self.morning_message_hour = 5
        self.morning_message_minute = 0
        self.morning_message_sent = False
        
        # Night message at 12:00 AM
        self.night_message_hour = 0
        self.night_message_minute = 0
        self.night_message_sent = False
        
        # Track sent messages to avoid duplicates
        self.session_start_sent_for_session = {}  # {channel_id: session_time}
        self.break_message_sent_for_session = {}  # {channel_id: session_time}

        # Session tracking
        self.current_session = ""
        self.last_session_check = None
        self.session_ended = True
        self.waiting_for_win = False
        self.last_prediction_was_loss = False
        self.in_break_period = False
        self.night_mode = False
        self.session_wins = 0
        self.session_losses = 0
        self.consecutive_wins = 0
        self.consecutive_losses = 0

        # Custom Break Duration
        self.custom_break_duration = 60

        # Channel management
        self.active_channels = []
        self.channel_configs = {}
        self.channel_prediction_status = {}
        self.channel_subscriptions = {}
        
        # Per-channel custom schedule times (format: ["HH:MM", "HH:MM"])
        self.channel_custom_schedules = {}  # {channel_id: [start_time, end_time, ...]}

        # Prediction message tracking - FIXED: Store message info with sent_via flag
        self.prediction_message_ids = {}  # {channel_id: {period: {'message_id': id, 'sent_via_user': bool}}}
        self.loss_prediction_history = {}  # {channel_id: [{'period': period, 'message_id': id, 'sent_via_user': bool}]}
        self.cycle_prediction_ids = {}
        self.max_loss_predictions_keep = 3

        # Break control
        self.pending_break = False
        self.pending_break_next_session = None

        # Track last sent message
        self.last_sent_period = None
        self.last_prediction_time = None

        # Single prediction mode
        self.current_prediction_period = None
        self.current_prediction_choice = None
        self.waiting_for_result = False
        self.break_message_sent = False
        self.last_result_was_win = False
        self.break_start_time = None
        self.session_start_sent = False

        # Prediction tracking
        self.last_processed_period = None
        self.predictions = {}
        self.user_state = {}
        self.session_predictions = []

        # Advanced prediction tracking
        self.prediction_history = []
        self.last_10_results = []
        self.pattern_memory = deque(maxlen=1000)
        self.number_memory = deque(maxlen=1000)
        self.recent_results = deque(maxlen=200)
        self.recent_numbers = deque(maxlen=200)
        self.big_small_history = deque(maxlen=500)
        self.number_distribution = {i: 0 for i in range(10)}
        self.last_actual_results = deque(maxlen=100)

        # ============= AI PATTERN RECOGNITION =============
        self.ai_model = None
        self.scaler = None
        self.pattern_history = []
        self.successful_patterns = []
        self.failed_patterns = []
        self.learning_rate = 0.1
        self.pattern_database = {}
        self.ai_confidence_threshold = 0.75
        self.min_training_samples = 100
        
        self.pattern_window_size = 20
        self.feature_count = 15
        self.ai_prediction_history = deque(maxlen=200)
        
        self.pattern_weights = {
            'streak_breaker': 0.25,
            'balance_correction': 0.35,
            'gap_filling': 0.25,
            'number_pattern': 0.10,
            'alternating': 0.05,
            'random_walk': 0.15,
            'history_trend': 0.20,
            'ai_pattern': 0.45
        }

        self.learning_history = deque(maxlen=1000)
        self.last_winning_strategy = None
        self.strategy_success_count = {}
        self.recent_patterns = deque(maxlen=100)
        self.prediction_streak_threshold = 3
        
        self.ai_correct_predictions = 0
        self.ai_total_predictions = 0
        self.ai_accuracy = 0.0
        self.ai_learning_cycles = 0
        self.last_ai_pattern_used = None
        
        self.pattern_types = {
            'alternating': 0,
            'streak': 0,
            'zigzag': 0,
            'cluster': 0,
            'random': 0,
            'cycle': 0
        }

        # Media and messages storage
        self.event_media = {}
        self.custom_messages = {}
        self.media_group_messages = {}
        self.scheduled_tasks = {}
        self.sent_custom_messages_in_break = {}
        
        self.message_types = {
            'session_start': 'Session Start',
            'break': 'Break',
            'good_morning': 'Good Morning',
            'good_night': 'Good Night',
            'win': 'Win Result',
            'loss': 'Loss Result',
            'prediction': 'Prediction',
            'custom': 'Custom'
        }

        # Default message templates with 12-hour format - FIXED: Removed <emoji> tags for regular emojis
        self.default_templates = {
            "good_morning": """
<blockquote>🔥<b>𝗚𝗢𝗢𝗗 𝗠𝗢𝗥𝗡𝗜𝗡𝗚 𝗪𝗜𝗡𝗡𝗘𝗥𝗦</b>🔥</blockquote>

🌅 <b>Welcome to a new winning session</b>
⏰ <b>Prediction Time:</b> {prediction_times}
✅ <b>Accuracy mode active</b>
➡️ <b>Get ready for today's signals</b>

🌟 <b>Today's Schedule:</b>
{schedule_list}
""",
            "good_night": """
<blockquote>🌙<b>𝗚𝗢𝗢𝗗 𝗡𝗜𝗚𝗛𝗧 𝗪𝗜𝗡𝗡𝗘𝗥𝗦</b>🌙</blockquote>

💤 <b>Today's prediction session has ended</b>
🏆 <b>Wins:</b> {wins}   <b>Losses:</b> {losses}
📊 <b>Win Rate:</b> {win_rate:.1f}%
⏰ <b>Next Start:</b> {next_start}

🔄 <b>See you tomorrow at the next session</b>
""",
            "break_message": """
<blockquote>⏰<b>𝗕𝗥𝗘𝗔𝗞 𝗧𝗜𝗠𝗘</b>⏰</blockquote>

⏰ <b>Break Duration:</b> {break_duration} Minutes
➡️ <b>Next Session:</b> {next_session}
✅ <b>Please wait for the next accurate prediction</b>

🔄 <b>We will be back soon</b>
""",
            "new_session": """
<blockquote>🔥<b>𝗡𝗘𝗪 𝗦𝗘𝗦𝗦𝗜𝗢𝗡 𝗦𝗧𝗔𝗥𝗧𝗘𝗗</b>🔥</blockquote>

⏰ <b>Session:</b> {session}
✅ <b>Prediction mode is now active</b>
➡️ <b>Stay ready for the next signal</b>
""",
            "single_prediction": """
<blockquote>💰<b>𝗧𝗘𝗔𝗠 𝗟𝗜𝗚𝗔𝗦𝗦 1 MINUTE OFFICIAL</b>💰</blockquote>

🔥 <b>ᴡɪɴɢᴏ ❶ ᴍɪɴᴜᴛᴇ</b> 🔥

✅ <b><u>{period}</u></b> ➡️ <a href="{register_link}"><b>{prediction}</b></a>
"""
        }
        self.custom_break_messages = {}
        self.custom_break_schedules = {}
        
        # Initialize all systems
        self.initialize_configs()
        self.initialize_ai_model()

    # ============= DATABASE METHODS =============
    
    def _init_mongo(self):
        """Initialize MongoDB connection."""
        try:
            self.mongo_client = MongoClient(self.mongo_uri, serverSelectionTimeoutMS=8000)
            self.mongo_db = self.mongo_client[self.mongo_db_name]
            self.mongo_client.admin.command('ping')
            logging.info(f"✅ MongoDB connected for {self.bot_name}")
        except Exception as e:
            logging.error(f"❌ MongoDB connection failed for {self.bot_name}: {e}")
            self.mongo_client = None
            self.mongo_db = None

    def _mongo_get_doc(self, doc_type):
        """Get document from MongoDB"""
        if self.mongo_db is None:
            return None
        try:
            return self.mongo_db.bot_data.find_one({'bot_name': self.bot_name, 'type': doc_type})
        except Exception as e:
            logging.error(f"❌ Mongo read failed ({doc_type}): {e}")
            return None

    def _mongo_upsert_doc(self, doc_type, data):
        """Insert or update document in MongoDB"""
        if self.mongo_db is None:
            return False
        try:
            self.mongo_db.bot_data.update_one(
                {'bot_name': self.bot_name, 'type': doc_type},
                {'$set': {
                    'bot_name': self.bot_name,
                    'type': doc_type,
                    'data': data,
                    'updated_at': datetime.utcnow()
                }},
                upsert=True
            )
            return True
        except Exception as e:
            logging.error(f"❌ Mongo write failed ({doc_type}): {e}")
            return False

    # ============= HELPER METHODS =============
    
    def format_time_12h(self, hour, minute):
        """Convert 24-hour format to 12-hour format with AM/PM"""
        mer = "AM" if hour < 12 else "PM"
        h = hour % 12
        if h == 0:
            h = 12
        return f"{h:02d}:{minute:02d} {mer}"

    def format_time_str_12h(self, time_str):
        """Convert time string to 12-hour format"""
        try:
            hour, minute = map(int, time_str.split(':'))
            return self.format_time_12h(hour, minute)
        except:
            return time_str

    def get_ist_now(self):
        """Get current time in IST (UTC+5:30)"""
        utc_now = datetime.utcnow()
        return utc_now + timedelta(hours=5, minutes=30)

    def get_channel_schedule_info(self, channel_id):
        """Get schedule info for a specific channel"""
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            return self.channel_custom_schedules[channel_id]
        return None

    def is_channel_active(self, channel_id):
        """Check if a channel should be active based on its custom schedule or global schedule"""
        now = self.get_ist_now()
        current_time = now.hour * 60 + now.minute
        
        # Check for custom schedule
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            schedule = self.channel_custom_schedules[channel_id]
            for time_slot in schedule:
                try:
                    start_str, end_str = time_slot.split('-')
                    start_hour, start_min = map(int, start_str.split(':'))
                    end_hour, end_min = map(int, end_str.split(':'))
                    
                    start_time = start_hour * 60 + start_min
                    end_time = end_hour * 60 + end_min
                    
                    if start_time <= current_time < end_time:
                        return True
                except:
                    continue
            return False
        
        # Fallback to global schedule
        day_start = self.prediction_start_hour * 60
        day_end = self.prediction_end_hour * 60
        
        if current_time < day_start or current_time >= day_end:
            return False
        
        minute_in_hour = now.minute
        if minute_in_hour < self.prediction_active_minutes:
            return True
        return False

    def get_current_session_info_for_channel(self, channel_id):
        """Get current session information for a specific channel"""
        if not self.is_channel_active(channel_id):
            return False, None, None, None, 0, None
        
        now = self.get_ist_now()
        current_hour = now.hour
        current_minute = now.minute
        
        # Check if we're in custom schedule
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            schedule = self.channel_custom_schedules[channel_id]
            for time_slot in schedule:
                try:
                    start_str, end_str = time_slot.split('-')
                    start_hour, start_min = map(int, start_str.split(':'))
                    end_hour, end_min = map(int, end_str.split(':'))
                    
                    start_time = start_hour * 60 + start_min
                    end_time = end_hour * 60 + end_min
                    current_time = current_hour * 60 + current_minute
                    
                    if start_time <= current_time < end_time:
                        session_start = self.format_time_str_12h(start_str)
                        session_end = self.format_time_str_12h(end_str)
                        next_session = None
                        minutes_until_next = end_time - current_time
                        return True, session_start, session_end, next_session, minutes_until_next, time_slot
                except:
                    continue
            return False, None, None, None, 0, None
        
        # Global schedule
        minute_in_hour = now.minute
        
        if minute_in_hour < self.prediction_active_minutes:
            is_active = True
            session_start = self.format_time_12h(current_hour, 0)
            session_end = self.format_time_12h(current_hour, self.prediction_active_minutes)
            next_session = self.format_time_12h(current_hour, self.prediction_active_minutes)
            minutes_until_next = self.prediction_active_minutes - minute_in_hour
        else:
            is_active = False
            session_start = None
            session_end = None
            next_hour = current_hour + 1 if current_hour < 23 else 6
            next_session = self.format_time_12h(next_hour, 0)
            minutes_until_next = (60 - minute_in_hour) + (0 if next_hour != 6 else (24 - current_hour) * 60)
        
        return is_active, session_start, session_end, next_session, minutes_until_next, None

    def get_session_name_for_channel(self, channel_id):
        """Get current session name for a specific channel"""
        is_active, session_start, session_end, _, _, time_slot = self.get_current_session_info_for_channel(channel_id)
        if is_active:
            if time_slot:
                return f"{session_start}-{session_end}"
            return f"{session_start}-{session_end}"
        return "BREAK"
    
    def get_session_key(self, channel_id, session_time):
        """Generate unique session key for tracking"""
        return f"{channel_id}:{session_time}"

    def get_channel_prediction_times_text(self, channel_id):
        """Get formatted prediction times text for channel"""
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            times = []
            for slot in self.channel_custom_schedules[channel_id]:
                try:
                    start, end = slot.split('-')
                    start_12h = self.format_time_str_12h(start)
                    end_12h = self.format_time_str_12h(end)
                    times.append(f"🔔 {start_12h} - {end_12h}")
                except:
                    times.append(f"🔔 {slot}")
            return "\n".join(times)
        else:
            # Global schedule
            times = []
            for hour in range(self.prediction_start_hour, self.prediction_end_hour):
                if hour >= self.prediction_start_hour and hour < self.prediction_end_hour:
                    start_12h = self.format_time_12h(hour, 0)
                    end_12h = self.format_time_12h(hour, self.prediction_active_minutes)
                    times.append(f"🔔 {start_12h} - {end_12h}")
            return "\n".join(times)

    def get_channel_schedule_list_text(self, channel_id):
        """Get formatted schedule list for channel"""
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            lines = []
            for i, slot in enumerate(self.channel_custom_schedules[channel_id], 1):
                try:
                    start, end = slot.split('-')
                    start_12h = self.format_time_str_12h(start)
                    end_12h = self.format_time_str_12h(end)
                    lines.append(f"• {start_12h} - {end_12h} (Prediction)")
                except:
                    lines.append(f"• {slot} (Prediction)")
            return "\n".join(lines)
        else:
            lines = []
            for hour in range(self.prediction_start_hour, self.prediction_end_hour):
                if hour >= self.prediction_start_hour and hour < self.prediction_end_hour:
                    start_12h = self.format_time_12h(hour, 0)
                    end_12h = self.format_time_12h(hour, self.prediction_active_minutes)
                    break_start_12h = self.format_time_12h(hour, self.prediction_active_minutes)
                    break_end_12h = self.format_time_12h(hour, self.prediction_active_minutes + self.prediction_break_minutes) if hour < self.prediction_end_hour - 1 else None
                    lines.append(f"• {start_12h} - {end_12h} Prediction")
                    if break_end_12h and hour < self.prediction_end_hour - 1:
                        lines.append(f"  {break_start_12h} - {break_end_12h} Break")
            return "\n".join(lines)

    # ============= API DATA FETCHING =============
    
    async def fetch_live_data(self):
        """Fetch live data from working API"""
        url = "https://draw.ar-lottery01.com/WinGo/WinGo_1M/GetHistoryIssuePage.json"
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
            'Accept': 'application/json, text/plain, */*',
            'Accept-Language': 'en-US,en;q=0.9',
            'Origin': 'https://draw.ar-lottery01.com',
            'Referer': 'https://draw.ar-lottery01.com/',
            'Accept-Encoding': 'gzip, deflate, br',
            'Connection': 'keep-alive'
        }
        
        max_retries = 3
        for attempt in range(max_retries):
            try:
                timeout = aiohttp.ClientTimeout(total=15, connect=10)
                async with aiohttp.ClientSession(timeout=timeout) as session:
                    async with session.get(url, headers=headers) as response:
                        if response.status != 200:
                            if attempt < max_retries - 1:
                                await asyncio.sleep(2 ** attempt)
                                continue
                            return None
                        
                        try:
                            data = await response.json()
                        except:
                            text = await response.text()
                            try:
                                data = json.loads(text)
                            except:
                                if attempt < max_retries - 1:
                                    await asyncio.sleep(2 ** attempt)
                                    continue
                                return None
                        
                        if data.get('data') and data['data'].get('list'):
                            data_list = data['data']['list']
                            formatted_data = []
                            
                            for item in data_list:
                                try:
                                    number_str = str(item.get('number', '0'))
                                    number_clean = ''.join(filter(str.isdigit, number_str))
                                    number = int(number_clean[0]) if number_clean else 0
                                    
                                    formatted_item = {
                                        'issueNumber': item.get('issueNumber'),
                                        'number': number,
                                        'color': self.get_color(number),
                                        'big_small': self.get_big_small(number),
                                        'premium': item.get('premium', ''),
                                        'sum': item.get('sum', '')
                                    }
                                    formatted_data.append(formatted_item)
                                except Exception:
                                    continue
                            
                            for item in formatted_data[:20]:
                                self.pattern_memory.append({
                                    'result': item['big_small'],
                                    'number': item['number'],
                                    'timestamp': datetime.now()
                                })
                                self.number_memory.append(item['number'])
                                self.recent_results.append(item['big_small'])
                                self.recent_numbers.append(item['number'])
                                self.big_small_history.append(item['big_small'])
                                self.number_distribution[item['number']] += 1
                                self.last_actual_results.append(item['big_small'])
                            
                            return formatted_data
                        
                        return None
                        
            except asyncio.TimeoutError:
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                else:
                    return None
            except Exception as e:
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
                else:
                    return None
        
        return None

    def get_big_small(self, num):
        return 'SMALL' if num <= 4 else 'BIG'

    def get_color(self, num):
        if num == 0:
            return 'GREEN'
        elif num in [1, 3, 5, 7, 9]:
            return 'RED'
        else:
            return 'VIOLET'

    def get_next_period(self, current_period):
        try:
            return str(int(current_period) + 1)
        except:
            import re
            numbers = re.findall(r'\d+', current_period)
            return str(int(numbers[-1]) + 1) if numbers else "000001"

    # ============= AI PATTERN RECOGNITION =============
    
    def initialize_ai_model(self):
        """Initialize AI model for pattern recognition"""
        try:
            if os.path.exists(self.ai_model_file):
                with open(self.ai_model_file, 'rb') as f:
                    saved_data = pickle.load(f)
                    self.ai_model = saved_data.get('model')
                    self.scaler = saved_data.get('scaler')
                    self.pattern_database = saved_data.get('pattern_database', {})
                    self.ai_accuracy = saved_data.get('ai_accuracy', 0.0)
                    self.ai_correct_predictions = saved_data.get('ai_correct_predictions', 0)
                    self.ai_total_predictions = saved_data.get('ai_total_predictions', 0)
                logging.info(f"✅ AI Model loaded: Accuracy = {self.ai_accuracy:.2%}")
            else:
                self.ai_model = RandomForestClassifier(
                    n_estimators=100,
                    max_depth=10,
                    random_state=42,
                    n_jobs=-1
                )
                self.scaler = StandardScaler()
                self.pattern_database = {}
                logging.info("✅ New AI Model created")
                
            mongo_doc = self._mongo_get_doc('pattern_history')
            if mongo_doc and isinstance(mongo_doc.get('data'), list):
                self.pattern_history = mongo_doc['data']
                logging.info(f"✅ Pattern history loaded from MongoDB: {len(self.pattern_history)} patterns")
            elif os.path.exists(self.pattern_history_file):
                with open(self.pattern_history_file, 'r', encoding='utf-8') as f:
                    self.pattern_history = json.load(f)
                self._mongo_upsert_doc('pattern_history', self.pattern_history)
                logging.info(f"✅ Pattern history migrated from JSON: {len(self.pattern_history)} patterns")
                
        except Exception as e:
            logging.error(f"❌ Error initializing AI model: {e}")
            self.ai_model = RandomForestClassifier(
                n_estimators=100,
                max_depth=10,
                random_state=42,
                n_jobs=-1
            )
            self.scaler = StandardScaler()
            self.pattern_database = {}

    def extract_features_for_ai(self, results, numbers):
        """Extract features for AI prediction"""
        features = []
        
        if len(results) < self.pattern_window_size:
            return [0] * self.feature_count
        
        result_numeric = [1 if r == 'BIG' else 0 for r in results]
        recent_results = result_numeric[:self.pattern_window_size]
        recent_numbers = numbers[:self.pattern_window_size]
        
        current_streak = 1
        for i in range(1, len(recent_results)):
            if recent_results[i] == recent_results[i-1]:
                current_streak += 1
            else:
                break
        features.append(current_streak)
        
        features.append(np.mean(recent_results[:3]))
        features.append(np.mean(recent_results[:5]))
        features.append(np.mean(recent_results[:10]))
        
        big_count = sum(recent_results)
        small_count = len(recent_results) - big_count
        features.append(big_count)
        features.append(small_count)
        features.append(big_count - small_count)
        
        big_numbers = sum(1 for n in recent_numbers if n >= 5)
        small_numbers = len(recent_numbers) - big_numbers
        features.append(big_numbers)
        features.append(small_numbers)
        
        alternating_score = 0
        for i in range(1, len(recent_results)):
            if recent_results[i] != recent_results[i-1]:
                alternating_score += 1
        features.append(alternating_score / len(recent_results))
        
        last_big_gap = 0
        last_small_gap = 0
        for i, r in enumerate(recent_results):
            if r == 1 and last_big_gap == 0:
                last_big_gap = i + 1
            if r == 0 and last_small_gap == 0:
                last_small_gap = i + 1
        features.append(last_big_gap)
        features.append(last_small_gap)
        
        number_counts = [recent_numbers.count(i) for i in range(10)]
        features.extend(number_counts[:3])
        
        pattern_hash = self.calculate_pattern_hash(recent_results)
        pattern_score = self.pattern_database.get(pattern_hash, {}).get('success_rate', 0.5)
        features.append(pattern_score)
        
        if len(recent_results) >= 5:
            trend = np.polyfit(range(5), recent_results[:5], 1)[0]
            features.append(trend)
        else:
            features.append(0)
        
        changes = sum(1 for i in range(1, len(recent_results)) 
                     if recent_results[i] != recent_results[i-1])
        features.append(changes / len(recent_results))
        
        if len(features) < self.feature_count:
            features.extend([0] * (self.feature_count - len(features)))
        elif len(features) > self.feature_count:
            features = features[:self.feature_count]
            
        return features

    def calculate_pattern_hash(self, pattern):
        pattern_str = ''.join(str(int(x)) for x in pattern)
        return hashlib.md5(pattern_str.encode()).hexdigest()[:10]

    def identify_pattern_type(self, pattern):
        pattern = list(pattern)
        
        alternating = True
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1]:
                alternating = False
                break
        if alternating and len(pattern) >= 3:
            return 'alternating'
        
        streak_count = 1
        max_streak = 1
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1]:
                streak_count += 1
                max_streak = max(max_streak, streak_count)
            else:
                streak_count = 1
        if max_streak >= 3:
            return 'streak'
        
        changes = sum(1 for i in range(1, len(pattern)) if pattern[i] != pattern[i-1])
        if changes >= len(pattern) * 0.7:
            return 'zigzag'
        
        clusters = 0
        in_cluster = False
        for i in range(1, len(pattern)):
            if pattern[i] == pattern[i-1] and not in_cluster:
                clusters += 1
                in_cluster = True
            elif pattern[i] != pattern[i-1]:
                in_cluster = False
        if clusters >= 2:
            return 'cluster'
        
        return 'random'

    def learn_from_pattern(self, pattern_hash, prediction, was_correct):
        if pattern_hash not in self.pattern_database:
            self.pattern_database[pattern_hash] = {
                'pattern': pattern_hash,
                'total_occurrences': 0,
                'correct_predictions': 0,
                'last_seen': datetime.now().isoformat(),
                'prediction_history': []
            }
        
        pattern_data = self.pattern_database[pattern_hash]
        pattern_data['total_occurrences'] += 1
        
        if was_correct:
            pattern_data['correct_predictions'] += 1
        
        pattern_data['success_rate'] = pattern_data['correct_predictions'] / pattern_data['total_occurrences']
        pattern_data['last_seen'] = datetime.now().isoformat()
        pattern_data['prediction_history'].append({
            'prediction': prediction,
            'was_correct': was_correct,
            'timestamp': datetime.now().isoformat()
        })
        
        if len(pattern_data['prediction_history']) > 50:
            pattern_data['prediction_history'] = pattern_data['prediction_history'][-50:]
        
        self.ai_total_predictions += 1
        if was_correct:
            self.ai_correct_predictions += 1
        
        self.ai_accuracy = self.ai_correct_predictions / self.ai_total_predictions if self.ai_total_predictions > 0 else 0
        
        pattern_type = self.identify_pattern_type([int(c) for c in pattern_hash[:10] if c.isdigit()])
        if pattern_type in self.pattern_types:
            self.pattern_types[pattern_type] += 1
        
        self.pattern_history.append({
            'pattern_hash': pattern_hash,
            'prediction': prediction,
            'was_correct': was_correct,
            'timestamp': datetime.now().isoformat(),
            'ai_confidence': getattr(self, 'last_ai_confidence', 0.5)
        })
        
        if len(self.pattern_history) > 1000:
            self.pattern_history = self.pattern_history[-1000:]
        
        if self.ai_total_predictions % 50 == 0:
            self.retrain_ai_model()

    def retrain_ai_model(self):
        if len(self.pattern_history) < self.min_training_samples:
            return
        
        try:
            logging.info(f"🔄 Retraining AI model with {len(self.pattern_history)} samples...")
            
            X_train = []
            y_train = []
            
            for pattern_data in self.pattern_history:
                if 'features' in pattern_data:
                    X_train.append(pattern_data['features'])
                    y_train.append(1 if pattern_data['was_correct'] else 0)
            
            if len(X_train) < self.min_training_samples:
                return
            
            X_train_array = np.array(X_train)
            y_train_array = np.array(y_train)
            
            self.scaler.fit(X_train_array)
            X_train_scaled = self.scaler.transform(X_train_array)
            
            self.ai_model.fit(X_train_scaled, y_train_array)
            
            self.ai_learning_cycles += 1
            logging.info(f"✅ AI Model retrained. Learning cycle: {self.ai_learning_cycles}")
            self.save_ai_model()
            
        except Exception as e:
            logging.error(f"❌ Error retraining AI model: {e}")

    def predict_with_ai(self, results, numbers):
        try:
            if len(results) < self.pattern_window_size:
                return None, 0.5
            
            features = self.extract_features_for_ai(results, numbers)
            
            if len(features) < self.feature_count:
                return None, 0.5
            
            features_array = np.array([features])
            
            if hasattr(self.scaler, 'scale_'):
                features_scaled = self.scaler.transform(features_array)
            else:
                features_scaled = features_array
            
            if hasattr(self.ai_model, 'predict_proba'):
                proba = self.ai_model.predict_proba(features_scaled)[0]
                prediction_proba = max(proba)
                prediction_class = self.ai_model.predict(features_scaled)[0]
            else:
                return None, 0.5
            
            prediction = 'BIG' if prediction_class == 1 else 'SMALL'
            
            result_numeric = [1 if r == 'BIG' else 0 for r in results[:self.pattern_window_size]]
            pattern_hash = self.calculate_pattern_hash(result_numeric)
            
            self.last_ai_pattern_used = {
                'pattern_hash': pattern_hash,
                'prediction': prediction,
                'confidence': float(prediction_proba),
                'features': features
            }
            
            return prediction, float(prediction_proba)
            
        except Exception as e:
            logging.error(f"❌ AI Prediction error: {e}")
            return None, 0.5

    def analyze_pattern_advanced(self, data_list):
        if not data_list or len(data_list) < 10:
            return random.choice(['BIG', 'SMALL']), 50
        
        recent_data = data_list[:50]
        results = [item['big_small'] for item in recent_data]
        numbers = [item['number'] for item in recent_data]
        
        ai_prediction, ai_confidence = self.predict_with_ai(results, numbers)
        
        patterns = self.detect_winning_patterns(results, numbers)
        strategies = self.calculate_winning_strategies(patterns)
        trad_prediction, trad_confidence = self.combine_winning_strategies(strategies)
        
        final_prediction = None
        final_confidence = 0
        
        if ai_prediction and ai_confidence > self.ai_confidence_threshold:
            final_prediction = ai_prediction
            final_confidence = ai_confidence * 100
        else:
            final_prediction = trad_prediction
            final_confidence = trad_confidence
        
        if self.consecutive_losses >= 2:
            final_prediction = 'BIG' if final_prediction == 'SMALL' else 'SMALL'
            final_confidence = max(final_confidence, 70)
        
        recent_predictions = list(self.big_small_history)
        if len(recent_predictions) >= 5 and all(p == final_prediction for p in recent_predictions[-5:]):
            final_prediction = 'BIG' if final_prediction == 'SMALL' else 'SMALL'
            final_confidence = max(60, final_confidence - 10)
        
        self.last_ai_confidence = ai_confidence if ai_prediction else 0
        
        return final_prediction, final_confidence

    def detect_winning_patterns(self, results, numbers):
        patterns = {}
        
        if len(results) < 10:
            return patterns
        
        current_streak = 1
        current_type = results[0]
        for i in range(1, len(results)):
            if results[i] == current_type:
                current_streak += 1
            else:
                break
        patterns['current_streak'] = current_streak
        patterns['streak_type'] = current_type
        
        last_20_results = results[:20]
        big_count_20 = last_20_results.count('BIG')
        small_count_20 = last_20_results.count('SMALL')
        patterns['big_20'] = big_count_20
        patterns['small_20'] = small_count_20
        patterns['imbalance_20'] = big_count_20 - small_count_20
        
        gap_big = 0
        gap_small = 0
        for i, r in enumerate(results[:10]):
            if r == 'BIG':
                gap_big = i
                break
        else:
            gap_big = 10
        
        for i, r in enumerate(results[:10]):
            if r == 'SMALL':
                gap_small = i
                break
        else:
            gap_small = 10
        patterns['gap_big'] = gap_big
        patterns['gap_small'] = gap_small
        
        if numbers and len(numbers) >= 15:
            recent_numbers = numbers[:15]
            big_nums = sum(1 for n in recent_numbers if n >= 5)
            small_nums = sum(1 for n in recent_numbers if n <= 4)
            patterns['big_nums_15'] = big_nums
            patterns['small_nums_15'] = small_nums
            patterns['number_imbalance'] = big_nums - small_nums
            
            number_counter = Counter(recent_numbers)
            hot_numbers = [num for num, count in number_counter.items() if count >= 2]
            patterns['hot_numbers'] = hot_numbers
        
        alternating_score = 0
        for i in range(2, min(10, len(results))):
            if results[i] != results[i-1]:
                alternating_score += 1
        patterns['alternating_score'] = alternating_score / 8.0
        
        return patterns

    def calculate_winning_strategies(self, patterns):
        strategies = []
        
        if patterns.get('current_streak', 0) >= 2:
            if patterns['current_streak'] >= 3:
                prediction = 'BIG' if patterns['streak_type'] == 'SMALL' else 'SMALL'
                confidence = min(90, 70 + (patterns['current_streak'] - 2) * 10)
                strategies.append(('streak_breaker', prediction, confidence))
        
        imbalance = patterns.get('imbalance_20', 0)
        if abs(imbalance) >= 3:
            if imbalance > 0:
                prediction = 'SMALL'
                confidence = min(85, 70 + abs(imbalance) * 3)
            else:
                prediction = 'BIG'
                confidence = min(85, 70 + abs(imbalance) * 3)
            strategies.append(('balance_correction', prediction, confidence))
        
        gap_diff = patterns.get('gap_big', 0) - patterns.get('gap_small', 0)
        if abs(gap_diff) >= 3:
            if gap_diff > 0:
                prediction = 'BIG'
                confidence = 75 + min(15, gap_diff * 3)
            else:
                prediction = 'SMALL'
                confidence = 75 + min(15, abs(gap_diff) * 3)
            strategies.append(('gap_filling', prediction, confidence))
        
        if patterns.get('alternating_score', 0) > 0.7 and self.last_actual_results:
            last_result = self.last_actual_results[0]
            prediction = 'BIG' if last_result == 'SMALL' else 'SMALL'
            confidence = 70
            strategies.append(('alternating_pattern', prediction, confidence))
        
        return strategies

    def combine_winning_strategies(self, strategies):
        if not strategies:
            return random.choice(['BIG', 'SMALL']), 50
        
        big_score = 0
        small_score = 0
        
        for strategy_name, prediction, confidence in strategies:
            weight = self.pattern_weights.get(strategy_name, 0.1)
            strategy_success = self.strategy_success_count.get(strategy_name, 0.5)
            adjusted_weight = weight * (0.5 + strategy_success)
            score = confidence * adjusted_weight
            
            if prediction == 'BIG':
                big_score += score
            else:
                small_score += score
        
        if self.consecutive_losses >= 2:
            if big_score > small_score:
                return 'SMALL', min(80, small_score + 20)
            else:
                return 'BIG', min(80, big_score + 20)
        
        if big_score > small_score:
            return 'BIG', min(95, big_score)
        else:
            return 'SMALL', min(95, small_score)

    def save_ai_model(self):
        try:
            saved_data = {
                'model': self.ai_model,
                'scaler': self.scaler,
                'pattern_database': self.pattern_database,
                'ai_accuracy': self.ai_accuracy,
                'ai_correct_predictions': self.ai_correct_predictions,
                'ai_total_predictions': self.ai_total_predictions
            }
            with open(self.ai_model_file, 'wb') as f:
                pickle.dump(saved_data, f)
            
            self._mongo_upsert_doc('pattern_history', self.pattern_history)
            logging.info(f"✅ AI Model saved: Accuracy = {self.ai_accuracy:.2%}")
        except Exception as e:
            logging.error(f"❌ Error saving AI model: {e}")

    # ============= MESSAGE FORMATTING =============
    
    def format_single_prediction(self, channel_id, period, prediction, for_channel=False):
        channel_config = self.get_channel_config(channel_id)
        template = self.get_channel_template(channel_id, 'single_prediction')
        
        if prediction == 'BIG':
            prediction_text = "𝗕𝗜𝗚"
        else:
            prediction_text = "𝗦𝗠𝗔𝗟𝗟"
        
        # Format period in bold
        period_str = str(period)
        if len(period_str) >= 4:
            period_display = period_str[-4:]
        else:
            period_display = period_str.zfill(4)
        
        period_text = f"𝟬{period_display[-3:]}" if len(period_display) == 4 else period_display
        
        format_dict = {
            'register_link': channel_config['register_link'],
            'period': period_text,
            'session': self.get_session_name_for_channel(channel_id),
            'prediction': prediction_text,
            'crown': "👑",
            'link': "🔗",
            'fire': "🔥",
            'sparkles': "✨",
            'rocket': "🚀",
            'money': "💰",
            'fire1': "🔥",
            'alarm1': "⏰",
            'tick': "✅",
            'rarrow': "➡️",
            'check': "✅",
            'chart': "📊",
            'target': "🎯",
            'trophy': "🏆",
            'gift': "🎁",
            'lightning': "⚡",
            'star': "⭐",
            'warning': "⚠️",
            'clock': "⏰",
            'moon': "🌙",
            'sun': "🌅",
            'coffee': "☕",
            'sleep': "💤",
            'break_icon': "⏸️",
            'reload': "🔄",
            'party': "🎉",
            'money_loss': "💸",
            'star2': "🌟"
        }
        
        formatted_text = template
        for k, v in format_dict.items():
            formatted_text = formatted_text.replace(f"{{{k}}}", str(v))
        
        return formatted_text

    # ============= MESSAGE SENDING METHODS =============
    
    async def send_message_with_retry(self, context, chat_id, text=None, max_retries=3, 
                                       for_channel=False, media_type=None, media_file=None, 
                                       caption=None, media_group=None, filename_hint=None):
        for attempt in range(max_retries):
            try:
                if media_group and len(media_group) == 1:
                    single = media_group[0]
                    media_type = single.get('type')
                    media_file = single.get('media')
                    caption = single.get('caption')
                    media_group = None

                has_media = bool(media_group or (media_type and media_file))

                # Try user account first if for_channel is True
                if for_channel and self.use_user_account and self.user_client_connected:
                    success = await self.send_via_user_account(
                        chat_id, text, media_type, media_file, caption, media_group, context, filename_hint
                    )
                    if success:
                        return success
                
                # Fallback to bot
                if media_group and len(media_group) > 1:
                    telegram_media = []
                    for i, media_item in enumerate(media_group):
                        mtype = media_item.get('type', 'photo')
                        caption_text = media_item.get('caption', '')
                        if mtype == 'photo':
                            media = InputMediaPhoto(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        elif mtype == 'video':
                            media = InputMediaVideo(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        elif mtype == 'animation':
                            media = InputMediaAnimation(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        else:
                            media = InputMediaDocument(
                                media=media_item['media'],
                                caption=caption_text if i == 0 else None,
                                parse_mode=ParseMode.HTML if caption_text else None
                            )
                        telegram_media.append(media)
                    
                    if telegram_media:
                        result = await context.bot.send_media_group(
                            chat_id=chat_id,
                            media=telegram_media
                        )
                        return result
                
                elif media_type and media_file:
                    # Handle stickers separately to avoid errors
                    if media_type == 'sticker':
                        result = await context.bot.send_sticker(
                            chat_id=chat_id,
                            sticker=media_file
                        )
                    elif media_type == 'photo':
                        result = await context.bot.send_photo(
                            chat_id=chat_id,
                            photo=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    elif media_type == 'video':
                        result = await context.bot.send_video(
                            chat_id=chat_id,
                            video=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    elif media_type == 'animation':
                        result = await context.bot.send_animation(
                            chat_id=chat_id,
                            animation=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    else:
                        result = await context.bot.send_document(
                            chat_id=chat_id,
                            document=media_file,
                            caption=caption,
                            parse_mode=ParseMode.HTML if caption else None
                        )
                    return result
                
                else:
                    if not text or not text.strip():
                        return False
                    result = await context.bot.send_message(
                        chat_id=chat_id,
                        text=text,
                        parse_mode=ParseMode.HTML
                    )
                    return result
                
            except NetworkError as e:
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
            except TimedOut as e:
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
            except RetryAfter as e:
                await asyncio.sleep(e.retry_after)
            except Exception as e:
                logging.error(f"Send error: {e}")
                if attempt < max_retries - 1:
                    await asyncio.sleep(2 ** attempt)
        
        return False

    async def send_via_user_account(self, chat_id, text=None, media_type=None, media_file=None, 
                                     caption=None, media_group=None, context=None, filename_hint=None):
        if not self.user_client_connected:
            return False

        chat_id_str = str(chat_id).strip()
        target_id = await self.get_chat_id(chat_id_str)
        
        if not target_id:
            logging.error(f"❌ Could not resolve chat ID for {chat_id}")
            return False
        
        try:
            # Detect actual media type from filename if needed
            if media_type and media_file and filename_hint:
                detected_type, actual_type = self.detect_media_type_from_file(filename_hint)
                if actual_type != 'document':
                    media_type = actual_type
            
            if media_group and len(media_group) > 1:
                pyrogram_media = []
                for i, media_item in enumerate(media_group):
                    file_id = media_item.get('media')
                    item_type = media_item.get('type', 'photo')
                    item_caption = media_item.get('caption', '') if i == 0 else None
                    
                    if item_type == 'photo':
                        media = PyrogramInputMediaPhoto(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    elif item_type == 'video':
                        media = PyrogramInputMediaVideo(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    elif item_type == 'animation':
                        media = PyrogramInputMediaAnimation(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    elif item_type == 'sticker':
                        # Send sticker separately
                        await self.user_app.send_sticker(
                            chat_id=target_id,
                            sticker=file_id
                        )
                        continue
                    else:
                        media = PyrogramInputMediaDocument(
                            media=file_id,
                            caption=item_caption,
                            parse_mode=PyrogramParseMode.HTML if item_caption else None
                        )
                    pyrogram_media.append(media)
                
                if pyrogram_media:
                    msgs = await self.user_app.send_media_group(
                        chat_id=target_id,
                        media=pyrogram_media
                    )
                    logging.info(f"✅ Media group sent to {chat_id}")
                    return msgs
            
            elif media_type and media_file:
                # Handle stickers specially
                if media_type == 'sticker':
                    msg = await self.user_app.send_sticker(
                        chat_id=target_id,
                        sticker=media_file
                    )
                elif media_type == 'photo':
                    msg = await self.user_app.send_photo(
                        chat_id=target_id,
                        photo=media_file,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'video':
                    msg = await self.user_app.send_video(
                        chat_id=target_id,
                        video=media_file,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                elif media_type == 'animation':
                    msg = await self.user_app.send_animation(
                        chat_id=target_id,
                        animation=media_file,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                else:
                    msg = await self.user_app.send_document(
                        chat_id=target_id,
                        document=media_file,
                        caption=caption if caption else None,
                        parse_mode=PyrogramParseMode.HTML if caption else None
                    )
                logging.info(f"✅ Media sent to {chat_id}")
                return msg
            
            else:
                if not text or not text.strip():
                    return False
                msg = await self.user_app.send_message(
                    chat_id=target_id,
                    text=text,
                    parse_mode=PyrogramParseMode.HTML
                )
                logging.info(f"✅ Text sent to {chat_id}")
                return msg
            
        except FloodWait as e:
            await asyncio.sleep(e.value)
            return False
        except Exception as e:
            logging.error(f"❌ User account send failed for {chat_id}: {e}")
            return False

    async def send_event_message(self, context, channel_id, event_type, **kwargs):
        event_type = self.normalize_event_type(event_type)

        custom_messages = self.get_custom_messages(channel_id, event_type)
        use_custom = custom_messages and len(custom_messages) > 0

        media_items = self.get_event_media(channel_id, event_type)
        
        # Send win/loss media immediately
        if event_type in ['win', 'loss'] and media_items:
            logging.info(f"📸 Sending {event_type} media to {channel_id}")
            await self.send_media_group(context, channel_id, media_items)
            return True

        if use_custom:
            for message_data in custom_messages:
                local_message_data = dict(message_data)
                if event_type == 'break':
                    local_message_data['send_order'] = 'media_first'
                elif event_type == 'session_start':
                    local_message_data['send_order'] = 'text_first'
                await self.send_stored_message(
                    context, channel_id, local_message_data,
                    session=kwargs.get('session', ''),
                    next_session=kwargs.get('next_session', ''),
                    wins=kwargs.get('wins', 0),
                    losses=kwargs.get('losses', 0),
                    win_rate=kwargs.get('win_rate', 0),
                    break_duration=kwargs.get('break_duration', self.custom_break_duration),
                    prediction_times=self.get_channel_prediction_times_text(channel_id),
                    schedule_list=self.get_channel_schedule_list_text(channel_id),
                    next_start=kwargs.get('next_start', '06:00 AM')
                )
            if media_items:
                if event_type == 'break':
                    await self.send_media_group(context, channel_id, media_items)
                else:
                    await self.send_media_group(context, channel_id, media_items)
            return True

        template_key = {
            'session_start': 'new_session',
            'break': 'break_message',
            'good_morning': 'good_morning',
            'good_night': 'good_night'
        }.get(event_type)
        
        if not template_key:
            return False
        
        template = self.get_channel_template(channel_id, template_key)
        channel_config = self.get_channel_config(channel_id)
        
        # Format next_session in 12-hour format
        next_session = kwargs.get('next_session', '')
        if next_session and ':' in next_session:
            try:
                hour, minute = map(int, next_session.split(':'))
                next_session = self.format_time_12h(hour, minute)
            except:
                pass
        
        # Get next start time for good night message
        next_start = "06:00 AM"
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            schedule = self.channel_custom_schedules[channel_id]
            if schedule:
                first_slot = schedule[0]
                try:
                    start_str = first_slot.split('-')[0]
                    next_start = self.format_time_str_12h(start_str)
                except:
                    pass
        
        format_dict = {
            'session': kwargs.get('session', ''),
            'next_session': next_session,
            'wins': kwargs.get('wins', 0),
            'losses': kwargs.get('losses', 0),
            'win_rate': kwargs.get('win_rate', 0),
            'break_duration': kwargs.get('break_duration', self.custom_break_duration),
            'register_link': channel_config['register_link'],
            'crown': "👑",
            'sparkles': "✨",
            'check': "✅",
            'chart': "📊",
            'link': "🔗",
            'sun': "🌅",
            'moon': "🌙",
            'sleep': "💤",
            'clock': "⏰",
            'reload': "🔄",
            'rocket': "🚀",
            'break_icon': "⏸️",
            'target': "🎯",
            'trophy': "🏆",
            'fire': "🔥",
            'money': "💰",
            'lightning': "⚡",
            'coffee': "☕",
            'gift': "🎁",
            'fire1': "🔥",
            'alarm1': "⏰",
            'tick': "✅",
            'rarrow': "➡️",
            'star2': "🌟",
            'prediction_times': self.get_channel_prediction_times_text(channel_id),
            'schedule_list': self.get_channel_schedule_list_text(channel_id),
            'next_start': next_start
        }
        
        try:
            formatted_text = template.format(**format_dict)
        except KeyError:
            formatted_text = template
        
        if not formatted_text or not formatted_text.strip():
            formatted_text = f"{event_type.replace('_', ' ').title()} update"
        
        if event_type == 'break' and media_items:
            await self.send_media_group(context, channel_id, media_items)

        await self.send_message_with_retry(
            context=context,
            chat_id=channel_id,
            text=formatted_text,
            for_channel=True
        )
        
        if event_type != 'break' and media_items:
            await self.send_media_group(context, channel_id, media_items)

        return True

    async def send_media_group(self, context, channel_id, media_items):
        """Send media group to channel"""
        if not media_items:
            return

        logging.info(f"📸 Sending {len(media_items)} media items to {channel_id}")

        if len(media_items) > 1:
            formatted_media_group = []
            for media_item in media_items:
                mtype = media_item.get('type', 'photo')
                fid = media_item.get('file_id')
                if fid:
                    # Skip stickers in media groups - send separately
                    if mtype == 'sticker':
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=self.use_user_account,
                            media_type='sticker',
                            media_file=fid,
                            filename_hint=media_item.get('file_name')
                        )
                        continue
                    formatted_media_group.append({
                        'type': mtype,
                        'media': fid,
                        'caption': None
                    })
            
            if formatted_media_group:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    for_channel=self.use_user_account,
                    media_group=formatted_media_group
                )
        else:
            media_item = media_items[0]
            await self.send_message_with_retry(
                context=context,
                chat_id=channel_id,
                for_channel=self.use_user_account,
                media_type=media_item.get('type', 'photo'),
                media_file=media_item.get('file_id'),
                caption=media_item.get('caption'),
                filename_hint=media_item.get('file_name')
            )

    async def send_single_prediction(self, context, channel_id, period, prediction):
        message_text = self.format_single_prediction(channel_id, period, prediction, for_channel=self.use_user_account)
        
        result = await self.send_message_with_retry(
            context=context,
            chat_id=channel_id,
            text=message_text,
            for_channel=self.use_user_account
        )
        
        if result:
            msg_id = self._extract_message_id(result)
            sent_via_user = self.use_user_account and self.user_client_connected
            if msg_id:
                if channel_id not in self.prediction_message_ids:
                    self.prediction_message_ids[channel_id] = {}
                self.prediction_message_ids[channel_id][period] = {
                    'message_id': msg_id,
                    'sent_via_user': sent_via_user
                }
                logging.info(f"📝 Stored prediction message_id {msg_id} for period {period} in channel {channel_id} (via_user={sent_via_user})")
        
        return result

    def _extract_message_id(self, result):
        if not result:
            return None
        try:
            if isinstance(result, list) and result:
                msg = result[0]
                return getattr(msg, 'id', None) or getattr(msg, 'message_id', None)
            return getattr(result, 'id', None) or getattr(result, 'message_id', None)
        except Exception:
            return None

    async def delete_channel_message(self, context, channel_id, message_id, sent_via_user=False):
        if not message_id:
            return False
        try:
            if sent_via_user and self.use_user_account and self.user_client_connected:
                target_id = await self.get_chat_id(str(channel_id).strip())
                if target_id:
                    await self.user_app.delete_messages(chat_id=target_id, message_ids=message_id)
                    logging.info(f'✅ Deleted via user account in {channel_id}: {message_id}')
                    return True
            await context.bot.delete_message(chat_id=channel_id, message_id=message_id)
            logging.info(f'✅ Deleted via bot in {channel_id}: {message_id}')
            return True
        except Exception as e:
            logging.warning(f"⚠️ Failed to delete message {message_id} in {channel_id}: {e}")
            return False

    async def track_loss_prediction(self, context, channel_id, period):
        """Track a loss prediction and delete oldest if more than 3"""
        message_info = self.prediction_message_ids.get(channel_id, {}).get(period)
        if not message_info:
            logging.warning(f"⚠️ No message_id found for loss prediction {period} in {channel_id}")
            return
        
        # Initialize loss history for channel if not exists
        if channel_id not in self.loss_prediction_history:
            self.loss_prediction_history[channel_id] = []
        
        # Add current loss prediction to history
        self.loss_prediction_history[channel_id].append({
            'period': period,
            'message_id': message_info['message_id'],
            'sent_via_user': message_info.get('sent_via_user', False)
        })
        logging.info(f"📌 Loss prediction tracked for {channel_id}: {period} -> {message_info['message_id']} | total={len(self.loss_prediction_history[channel_id])}")
        
        # Delete oldest if more than max allowed
        while len(self.loss_prediction_history[channel_id]) > self.max_loss_predictions_keep:
            oldest = self.loss_prediction_history[channel_id].pop(0)
            logging.info(f"🗑️ Deleting old loss prediction for {channel_id}: {oldest['period']} (ID: {oldest['message_id']})")
            await self.delete_channel_message(context, channel_id, oldest['message_id'], oldest.get('sent_via_user', False))

    async def clear_loss_history_on_win(self, channel_id):
        """Clear loss history on win"""
        if channel_id in self.loss_prediction_history and self.loss_prediction_history[channel_id]:
            cleared_count = len(self.loss_prediction_history[channel_id])
            self.loss_prediction_history[channel_id] = []
            logging.info(f"🎉 Win detected! Cleared {cleared_count} loss predictions for {channel_id}")
            return True
        return False

    def reset_loss_prediction_history(self, channel_id=None):
        """Reset loss prediction history"""
        if channel_id is None:
            self.loss_prediction_history = {}
        else:
            self.loss_prediction_history[channel_id] = []

    async def send_stored_message(self, context, channel_id, message_data, **placeholders):
        media_items = message_data.get('media_group', [])
        text_content = message_data.get('text', '')
        send_order = message_data.get('send_order', 'text_first')
        
        use_user_account = self.use_user_account
        
        if text_content:
            text_content = self.format_placeholders(text_content, channel_id, **placeholders)
            formatted_text = text_content
        else:
            formatted_text = None

        if send_order == 'combined' and media_items:
            formatted_media_group = []
            for i, media_item in enumerate(media_items):
                media_type = media_item.get('type', 'photo')
                file_id = media_item.get('file_id')
                if file_id:
                    caption = formatted_text if (formatted_text and i == 0) else None
                    formatted_media_group.append({
                        'type': media_type,
                        'media': file_id,
                        'caption': caption,
                        'file_name': media_item.get('file_name')
                    })
            
            if formatted_media_group:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    for_channel=bool(formatted_text),
                    media_group=formatted_media_group
                )
                
        elif send_order == 'text_first':
            if formatted_text:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    text=formatted_text,
                    for_channel=use_user_account
                )
            
            if media_items:
                if len(media_items) > 1:
                    formatted_media_group = []
                    for media_item in media_items:
                        media_type = media_item.get('type', 'photo')
                        file_id = media_item.get('file_id')
                        if file_id:
                            formatted_media_group.append({
                                'type': media_type,
                                'media': file_id,
                                'caption': None,
                                'file_name': media_item.get('file_name')
                            })
                    
                    if formatted_media_group:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=False,
                            media_group=formatted_media_group
                        )
                else:
                    media_item = media_items[0]
                    await self.send_message_with_retry(
                        context=context,
                        chat_id=channel_id,
                        for_channel=False,
                        media_type=media_item.get('type', 'photo'),
                        media_file=media_item.get('file_id'),
                        filename_hint=media_item.get('file_name')
                    )
                    
        elif send_order == 'media_first':
            if media_items:
                if len(media_items) > 1:
                    formatted_media_group = []
                    for media_item in media_items:
                        media_type = media_item.get('type', 'photo')
                        file_id = media_item.get('file_id')
                        if file_id:
                            formatted_media_group.append({
                                'type': media_type,
                                'media': file_id,
                                'caption': None,
                                'file_name': media_item.get('file_name')
                            })
                    
                    if formatted_media_group:
                        await self.send_message_with_retry(
                            context=context,
                            chat_id=channel_id,
                            for_channel=False,
                            media_group=formatted_media_group
                        )
                else:
                    media_item = media_items[0]
                    await self.send_message_with_retry(
                        context=context,
                        chat_id=channel_id,
                        for_channel=False,
                        media_type=media_item.get('type', 'photo'),
                        media_file=media_item.get('file_id'),
                        filename_hint=media_item.get('file_name')
                    )
            
            if formatted_text:
                await self.send_message_with_retry(
                    context=context,
                    chat_id=channel_id,
                    text=formatted_text,
                    for_channel=use_user_account
                )

    async def send_session_start_message(self, context, channel_id, session_info):
        """Send session start message for a specific channel"""
        session_key = self.get_session_key(channel_id, session_info)
        
        # Check if already sent
        if session_key in self.session_start_sent_for_session:
            return
        
        await self.send_event_message(
            context, channel_id, 'session_start',
            session=session_info
        )
        
        self.session_start_sent_for_session[session_key] = True
        logging.info(f"✅ Session start message sent to {channel_id} for {session_info}")

    async def send_break_message_for_channel(self, context, channel_id, session_info, next_session_info):
        """Send break message for a specific channel"""
        session_key = self.get_session_key(channel_id, session_info)
        
        # Check if already sent
        if session_key in self.break_message_sent_for_session:
            return
        
        await self.send_event_message(
            context, channel_id, 'break',
            next_session=next_session_info,
            break_duration=self.prediction_break_minutes
        )
        
        self.break_message_sent_for_session[session_key] = True
        logging.info(f"✅ Break message sent to {channel_id} for session {session_info}")

    async def send_good_morning_message(self, context):
        self.morning_message_sent = True
        self.night_message_sent = False
        self.session_ended = False
        self.in_break_period = False
        self.break_message_sent = False
        self.waiting_for_result = False
        self.last_result_was_win = False
        self.waiting_for_win = False
        self.session_start_sent = False
        
        # Reset session stats
        self.session_wins = 0
        self.session_losses = 0
        self.consecutive_losses = 0
        self.consecutive_wins = 0
        self.big_small_history.clear()
        
        # Reset tracking dictionaries
        self.session_start_sent_for_session.clear()
        self.break_message_sent_for_session.clear()
        
        if not self.active_channels:
            return
        
        success_count = 0
        for channel in self.active_channels:
            try:
                await self.send_event_message(context, channel, 'good_morning')
                success_count += 1
            except Exception as e:
                logging.error(f"❌ Failed to send morning message to {channel}: {e}")
        
        logging.info(f"✅ Good morning messages sent: {success_count}/{len(self.active_channels)}")

    async def send_good_night_message(self, context):
        self.night_message_sent = True
        self.morning_message_sent = False
        self.in_break_period = True
        self.break_message_sent = True

        total_predictions = self.session_wins + self.session_losses
        win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0

        if not self.active_channels:
            return

        success_count = 0
        for channel in self.active_channels:
            try:
                if not self.is_channel_prediction_active(channel):
                    continue

                await self.send_event_message(
                    context, channel, 'good_night',
                    wins=self.session_wins,
                    losses=self.session_losses,
                    win_rate=win_rate
                )
                success_count += 1

            except Exception as e:
                logging.error(f"❌ Failed to send night message to {channel}: {e}")

        logging.info(f"✅ Good night messages sent: {success_count}/{len(self.active_channels)}")

    # ============= PREDICTION RESULT HANDLING =============
    
    async def check_result_and_send_next(self, context, data):
        if not self.current_prediction_period or not self.waiting_for_result:
            return False
        
        result_found = False
        for item in data[:10]:
            if item['issueNumber'] == self.current_prediction_period:
                result = item['big_small']
                is_win = self.current_prediction_choice == result
                
                results = [item['big_small'] for item in data[:20]]
                numbers = [item['number'] for item in data[:20]]
                
                result_numeric = [1 if r == 'BIG' else 0 for r in results[:self.pattern_window_size]]
                if len(result_numeric) >= self.pattern_window_size:
                    pattern_hash = self.calculate_pattern_hash(result_numeric)
                    self.learn_from_pattern(pattern_hash, self.current_prediction_choice, is_win)
                
                if is_win:
                    self.session_wins += 1
                    self.consecutive_wins += 1
                    self.consecutive_losses = 0
                    self.last_prediction_was_loss = False
                    self.last_result_was_win = True
                    
                    # Clear loss history for all channels on win
                    for channel in self.active_channels:
                        if self.is_channel_prediction_active(channel) and self.is_channel_active(channel):
                            await self.clear_loss_history_on_win(channel)
                            logging.info(f"🎉 Sending win media to {channel}")
                            await self.send_event_message(context, channel, 'win')
                else:
                    self.session_losses += 1
                    self.consecutive_losses += 1
                    self.consecutive_wins = 0
                    self.last_prediction_was_loss = True
                    self.last_result_was_win = False
                    
                    # Track loss for all active channels
                    for channel in self.active_channels:
                        if self.is_channel_prediction_active(channel) and self.is_channel_active(channel):
                            # Track this loss prediction for deletion later
                            await self.track_loss_prediction(context, channel, self.current_prediction_period)
                            logging.info(f"❌ Sending loss media to {channel}")
                            await self.send_event_message(context, channel, 'loss')
                
                result_found = True
                break
        
        if result_found:
            latest = data[0]
            latest_period = latest.get('issueNumber')
            next_period = self.get_next_period(latest_period)
            
            choice, confidence = self.analyze_pattern_advanced(data)
            
            self.current_prediction_period = next_period
            self.current_prediction_choice = choice
            self.waiting_for_result = True
            
            # Send predictions only to active channels
            for channel in self.active_channels:
                if self.is_channel_prediction_active(channel) and self.is_channel_active(channel):
                    await self.send_single_prediction(context, channel, next_period, choice)
            
            return True
        
        return False

    async def send_first_prediction(self, context, data):
        if self.waiting_for_result:
            return False
        
        latest = data[0]
        latest_period = latest.get('issueNumber')
        next_period = self.get_next_period(latest_period)
        
        choice, confidence = self.analyze_pattern_advanced(data)
        
        self.current_prediction_period = next_period
        self.current_prediction_choice = choice
        self.waiting_for_result = True
        
        # Send predictions only to active channels
        for channel in self.active_channels:
            if self.is_channel_prediction_active(channel) and self.is_channel_active(channel):
                await self.send_single_prediction(context, channel, next_period, choice)
        
        return True

    # ============= CHANNEL MANAGEMENT =============
    
    def load_config(self):
        default_config = {
            "admin_ids": [6484788124],
            "channels": [],
            "channel_configs": {},
            "channel_prediction_status": {},
            "channel_subscriptions": {},
            "channel_custom_schedules": {},
            "custom_break_messages": {},
            "custom_break_schedules": {},
            "custom_break_duration": 60,
            "event_media": {},
            "api_url": "https://draw.ar-lottery01.com/WinGo/WinGo_1M/GetHistoryIssuePage.json"
        }

        try:
            mongo_doc = self._mongo_get_doc('config')
            if mongo_doc and isinstance(mongo_doc.get('data'), dict):
                loaded_config = mongo_doc['data']
                self.config = {**default_config, **loaded_config}
            elif os.path.exists(self.config_file):
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    loaded_config = json.load(f)
                self.config = {**default_config, **loaded_config}
                self._mongo_upsert_doc('config', loaded_config)
                logging.info("✅ Config migrated from JSON to MongoDB")
            else:
                self.config = default_config.copy()
                self.active_channels = []
                self.channel_configs = {}
                self.channel_prediction_status = {}
                self.channel_subscriptions = {}
                self.channel_custom_schedules = {}
                self.custom_break_messages = {}
                self.custom_break_schedules = {}
                self.event_media = {}
                self.save_config()
                logging.info("✅ Created new config in MongoDB")
                return

            self.active_channels = self.config.get('channels', [])
            self.channel_configs = self.config.get('channel_configs', {})
            self.channel_prediction_status = self.config.get('channel_prediction_status', {})
            self.channel_subscriptions = self.config.get('channel_subscriptions', {})
            self.channel_custom_schedules = self.config.get('channel_custom_schedules', {})
            self.custom_break_messages = self.config.get('custom_break_messages', {})
            self.custom_break_schedules = self.config.get('custom_break_schedules', {})
            self.custom_break_duration = self.config.get('custom_break_duration', 60)
            self.event_media = self.config.get('event_media', {})

            for channel_id, config in self.channel_configs.items():
                if 'templates' not in config or not isinstance(config.get('templates'), dict):
                    config['templates'] = {}
                for t_key, t_val in self.default_templates.items():
                    if t_key not in config['templates']:
                        config['templates'][t_key] = t_val

                if 'show_links' not in config:
                    config['show_links'] = True
                if 'show_promo' not in config:
                    config['show_promo'] = True
                if channel_id not in self.channel_prediction_status:
                    self.channel_prediction_status[channel_id] = True

            logging.info(f"✅ Configuration loaded. Active channels: {len(self.active_channels)}")
            logging.info(f"✅ Channels with custom schedules: {len(self.channel_custom_schedules)}")

        except Exception as e:
            logging.error(f"❌ Error loading config: {e}")
            self.config = default_config.copy()
            self.active_channels = []
            self.channel_configs = {}
            self.channel_prediction_status = {}
            self.channel_subscriptions = {}
            self.channel_custom_schedules = {}
            self.custom_break_messages = {}
            self.custom_break_schedules = {}
            self.event_media = {}
            self.save_config()

    def save_config(self):
        try:
            self.config['channels'] = self.active_channels
            self.config['channel_configs'] = self.channel_configs
            self.config['channel_prediction_status'] = self.channel_prediction_status
            self.config['channel_subscriptions'] = self.channel_subscriptions
            self.config['channel_custom_schedules'] = self.channel_custom_schedules
            self.config['custom_break_messages'] = self.custom_break_messages
            self.config['custom_break_schedules'] = self.custom_break_schedules
            self.config['custom_break_duration'] = self.custom_break_duration
            self.config['event_media'] = self.event_media

            if self._mongo_upsert_doc('config', self.config):
                logging.info(f"✅ Configuration saved to MongoDB")
        except Exception as e:
            logging.error(f"❌ Error saving config: {e}")

    def get_channel_config(self, channel_id):
        if channel_id not in self.channel_configs:
            self.channel_configs[channel_id] = {
                'register_link': "https://bdgsg.com//#/register?invitationCode=5151329947",
                'promotional_text': "🎁 Register now and get DAILY FREE GIFT CODE! 🎁",
                'show_links': True,
                'show_promo': True,
                'templates': self.default_templates.copy(),
                'custom_break_enabled': False,
                'custom_break_delay': 5,
                'custom_break_mode': 'sequential'
            }
            self.save_config()
        
        config = self.channel_configs[channel_id]
        if 'show_links' not in config:
            config['show_links'] = True
        if 'show_promo' not in config:
            config['show_promo'] = True
        if 'templates' not in config:
            config['templates'] = self.default_templates.copy()
            self.save_config()
        
        return config

    def update_channel_config(self, channel_id, updates):
        config = self.get_channel_config(channel_id)
        config.update(updates)
        self.channel_configs[channel_id] = config
        self.save_config()
        return config

    def get_channel_template(self, channel_id, template_key):
        config = self.get_channel_config(channel_id)
        return config['templates'].get(template_key, self.default_templates[template_key] if template_key in self.default_templates else '')

    def is_channel_prediction_active(self, channel_id):
        return self.channel_prediction_status.get(channel_id, True)

    def toggle_channel_prediction(self, channel_id):
        current = self.channel_prediction_status.get(channel_id, True)
        self.channel_prediction_status[channel_id] = not current
        self.save_config()
        return self.channel_prediction_status[channel_id]

    def set_channel_prediction_status(self, channel_id, status):
        self.channel_prediction_status[channel_id] = status
        self.save_config()
        return status

    def is_channel_enabled(self, channel_id):
        return self.is_channel_prediction_active(channel_id)

    def set_channel_subscription_days(self, channel_id, days):
        now = self.get_ist_now()
        expires = now + timedelta(days=max(1, int(days)))
        self.channel_subscriptions[channel_id] = {
            'days': int(days),
            'expires_at': expires.isoformat(),
            'alert_1d_sent': False,
            'expired_sent': False,
        }
        self.save_config()
        return self.channel_subscriptions[channel_id]

    def is_channel_subscription_active(self, channel_id):
        sub = self.channel_subscriptions.get(channel_id)
        if not sub:
            return True
        try:
            exp = datetime.fromisoformat(sub.get('expires_at'))
            return self.get_ist_now() < exp
        except Exception:
            return True

    # ============= CUSTOM SCHEDULE METHODS =============
    
    def set_channel_custom_schedule(self, channel_id, schedule_times):
        """Set custom prediction schedule for a channel
        schedule_times: list of strings like ["10:00-11:00", "14:00-15:00", "17:00-18:00", "20:00-21:00"]
        """
        self.channel_custom_schedules[channel_id] = schedule_times
        self.save_config()
        return True

    def add_channel_schedule_slot(self, channel_id, start_time, end_time):
        """Add a single schedule slot for a channel"""
        slot = f"{start_time}-{end_time}"
        if channel_id not in self.channel_custom_schedules:
            self.channel_custom_schedules[channel_id] = []
        if slot not in self.channel_custom_schedules[channel_id]:
            self.channel_custom_schedules[channel_id].append(slot)
            # Sort slots by start time
            self.channel_custom_schedules[channel_id].sort()
            self.save_config()
            return True
        return False

    def remove_channel_schedule_slot(self, channel_id, index):
        """Remove a schedule slot by index"""
        if channel_id in self.channel_custom_schedules:
            if 0 <= index < len(self.channel_custom_schedules[channel_id]):
                removed = self.channel_custom_schedules[channel_id].pop(index)
                if not self.channel_custom_schedules[channel_id]:
                    del self.channel_custom_schedules[channel_id]
                self.save_config()
                return True
        return False

    def clear_channel_custom_schedule(self, channel_id):
        """Remove all custom schedule slots for a channel"""
        if channel_id in self.channel_custom_schedules:
            del self.channel_custom_schedules[channel_id]
            self.save_config()
            return True
        return False

    def get_channel_schedule_display(self, channel_id):
        """Get formatted schedule display for a channel"""
        if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
            lines = []
            for i, slot in enumerate(self.channel_custom_schedules[channel_id], 1):
                try:
                    start, end = slot.split('-')
                    start_12h = self.format_time_str_12h(start)
                    end_12h = self.format_time_str_12h(end)
                    lines.append(f"{i}. {start_12h} - {end_12h}")
                except:
                    lines.append(f"{i}. {slot}")
            return "\n".join(lines)
        return "Using Global Schedule (06:00 AM - 12:00 AM, 50min prediction, 10min break)"

    # ============= CUSTOM MESSAGES MANAGEMENT =============
    
    def get_custom_messages(self, channel_id, message_type):
        if channel_id not in self.custom_messages:
            return []
        return self.custom_messages[channel_id].get(message_type, [])

    def add_custom_message_simple(self, channel_id, message_type, message_data):
        if channel_id not in self.custom_messages:
            self.custom_messages[channel_id] = {}
        if message_type not in self.custom_messages[channel_id]:
            self.custom_messages[channel_id][message_type] = []
        
        self.custom_messages[channel_id][message_type].append(message_data)
        self.save_custom_messages()
        return len(self.custom_messages[channel_id][message_type]) - 1

    def delete_custom_message(self, channel_id, message_type, index=None):
        if channel_id not in self.custom_messages or message_type not in self.custom_messages[channel_id]:
            return False
        
        if index is None:
            del self.custom_messages[channel_id][message_type]
            self.save_custom_messages()
            return True
        elif 0 <= index < len(self.custom_messages[channel_id][message_type]):
            self.custom_messages[channel_id][message_type].pop(index)
            if not self.custom_messages[channel_id][message_type]:
                del self.custom_messages[channel_id][message_type]
            self.save_custom_messages()
            return True
        return False

    def save_custom_messages(self):
        try:
            if self._mongo_upsert_doc('custom_messages', self.custom_messages):
                logging.info("✅ Custom messages saved to MongoDB")
        except Exception as e:
            logging.error(f"❌ Error saving custom messages: {e}")

    # ============= EVENT MEDIA MANAGEMENT =============
    
    def get_event_media(self, channel_id, event_type):
        """Get event media list with count display"""
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media:
            return []
        return self.event_media[channel_id].get(event_type, [])

    def add_event_media(self, channel_id, event_type, media_item):
        """Add event media and return count"""
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media:
            self.event_media[channel_id] = {}
        if event_type not in self.event_media[channel_id]:
            self.event_media[channel_id][event_type] = []
        
        self.event_media[channel_id][event_type].append(media_item)
        self.save_config()
        return len(self.event_media[channel_id][event_type])

    def delete_event_media(self, channel_id, event_type, index=None):
        """Delete event media by index or all"""
        event_type = self.normalize_event_type(event_type)
        if channel_id not in self.event_media or event_type not in self.event_media[channel_id]:
            return False
        
        if index is None:
            # Delete all media for this event type
            self.event_media[channel_id][event_type] = []
            self.save_config()
            return True
        elif 0 <= index < len(self.event_media[channel_id][event_type]):
            # Delete specific media
            self.event_media[channel_id][event_type].pop(index)
            self.save_config()
            return True
        return False

    def get_custom_break_messages(self, channel_id):
        messages = self.custom_break_messages.get(channel_id, [])
        if isinstance(messages, dict):
            messages = [messages]
        elif not isinstance(messages, list):
            messages = []
        return messages

    def get_custom_break_message_by_index(self, channel_id, index):
        messages = self.get_custom_break_messages(channel_id)
        if 0 <= index < len(messages):
            return messages[index]
        return None

    def add_custom_break_message(self, channel_id, message_data):
        if channel_id not in self.custom_break_messages:
            self.custom_break_messages[channel_id] = []
        if not isinstance(self.custom_break_messages[channel_id], list):
            self.custom_break_messages[channel_id] = []
        
        self.custom_break_messages[channel_id].append(message_data)
        self.save_config()
        return len(self.custom_break_messages[channel_id]) - 1

    def update_custom_break_message(self, channel_id, index, message_data):
        messages = self.get_custom_break_messages(channel_id)
        if 0 <= index < len(messages):
            self.custom_break_messages[channel_id][index] = message_data
            self.save_config()
            return True
        return False

    def delete_custom_break_message(self, channel_id, index=None):
        if channel_id in self.custom_break_messages:
            if index is None:
                del self.custom_break_messages[channel_id]
                self.save_config()
                return True
            elif isinstance(self.custom_break_messages[channel_id], list) and 0 <= index < len(self.custom_break_messages[channel_id]):
                self.custom_break_messages[channel_id].pop(index)
                if not self.custom_break_messages[channel_id]:
                    del self.custom_break_messages[channel_id]
                self.save_config()
                return True
        return False

    def get_next_custom_break_index(self, channel_id):
        channel_config = self.get_channel_config(channel_id)
        
        if channel_id not in self.custom_break_schedules:
            self.custom_break_schedules[channel_id] = 0
            self.save_config()
        
        messages = self.get_custom_break_messages(channel_id)
        if not messages:
            return None
        
        mode = channel_config.get('custom_break_mode', 'sequential')
        
        if mode == 'sequential':
            current_idx = self.custom_break_schedules[channel_id]
            self.custom_break_schedules[channel_id] = (current_idx + 1) % len(messages)
            self.save_config()
            return current_idx
        else:
            return random.randint(0, len(messages) - 1)

    def normalize_event_type(self, event_type):
        if event_type == 'session_end':
            return 'break'
        return event_type

    def format_placeholders(self, text, channel_id, **kwargs):
        if not text:
            return text

        channel_config = self.get_channel_config(channel_id)
        format_dict = {
            'register_link': channel_config.get('register_link', ''),
            'promo_text': channel_config.get('promotional_text', ''),
            'session': kwargs.get('session', ''),
            'next_session': kwargs.get('next_session', ''),
            'wins': kwargs.get('wins', 0),
            'losses': kwargs.get('losses', 0),
            'win_rate': kwargs.get('win_rate', 0),
            'break_duration': kwargs.get('break_duration', self.custom_break_duration),
            'period': kwargs.get('period', ''),
            'prediction': kwargs.get('prediction', ''),
            'prediction_times': kwargs.get('prediction_times', self.get_channel_prediction_times_text(channel_id)),
            'schedule_list': kwargs.get('schedule_list', self.get_channel_schedule_list_text(channel_id)),
            'next_start': kwargs.get('next_start', '06:00 AM')
        }

        for k, v in kwargs.items():
            if k not in format_dict:
                format_dict[k] = v

        for key, val in format_dict.items():
            text = text.replace(f"{{{key}}}", str(val))
        return text

    # ============= EMOJI HANDLING =============
    
    def load_emoji_config(self):
        default_emoji_config = {
            "premium_emojis": {
                "fire": "🔥",
                "crown": "👑",
                "sparkles": "✨",
                "rocket": "🚀",
                "money": "💰",
                "chart": "📊",
                "target": "🎯",
                "trophy": "🏆",
                "gift": "🎁",
                "lightning": "⚡",
                "star": "⭐",
                "warning": "⚠️",
                "check": "✅",
                "cross": "❌",
                "clock": "⏰",
                "link": "🔗",
                "moon": "🌙",
                "sun": "🌅",
                "coffee": "☕",
                "sleep": "💤",
                "break_icon": "⏸️",
                "reload": "🔄",
                "party": "🎉",
                "money_loss": "💸",
                "star2": "🌟",
                "fire1": "🔥",
                "alarm1": "⏰",
                "tick": "✅",
                "rarrow": "➡️",
                "bookmark": "🔖",
                "bell": "🔔",
                "specialoffer": "🎲🎲🎲🎲🎲🎲",
            },
            "regular_emojis": {
                "fire": "🔥",
                "crown": "👑",
                "sparkles": "✨",
                "rocket": "🚀",
                "money": "💰",
                "chart": "📊",
                "target": "🎯",
                "trophy": "🏆",
                "gift": "🎁",
                "lightning": "⚡",
                "star": "⭐",
                "warning": "⚠️",
                "check": "✅",
                "cross": "❌",
                "clock": "⏰",
                "link": "🔗",
                "moon": "🌙",
                "sun": "🌅",
                "coffee": "☕",
                "sleep": "💤",
                "break_icon": "⏸️",
                "reload": "🔄",
                "party": "🎉",
                "money_loss": "💸",
                "star2": "🌟",
                "fire1": "🔥",
                "alarm1": "⏰",
                "tick": "✅",
                "rarrow": "➡️",
                "bookmark": "🔖",
                "bell": "🔔",
                "specialoffer": "🎲🎲🎲🎲🎲🎲",
            },
            "emoji_to_placeholder": {
                "🔥": "{fire}",
                "👑": "{crown}",
                "✨": "{sparkles}",
                "🚀": "{rocket}",
                "💰": "{money}",
                "📊": "{chart}",
                "🎯": "{target}",
                "🏆": "{trophy}",
                "🎁": "{gift}",
                "⚡": "{lightning}",
                "⭐": "{star}",
                "⚠️": "{warning}",
                "✅": "{check}",
                "✅": "{tick}",
                "❌": "{cross}",
                "⏰": "{clock}",
                "🔗": "{link}",
                "🌙": "{moon}",
                "🌅": "{sun}",
                "☕": "{coffee}",
                "💤": "{sleep}",
                "🔥": "{fire1}",
                "⏰": "{alarm1}",
                "➡️": "{rarrow}",
                "⏸️": "{break_icon}",
                "🔄": "{reload}",
                "🎉": "{party}",
                "💸": "{money_loss}",
                "🌟": "{star2}",
            },
            "placeholder_to_emoji": {
                "{fire}": "🔥",
                "{crown}": "👑",
                "{sparkles}": "✨",
                "{rocket}": "🚀",
                "{money}": "💰",
                "{chart}": "📊",
                "{target}": "🎯",
                "{trophy}": "🏆",
                "{gift}": "🎁",
                "{lightning}": "⚡",
                "{star}": "⭐",
                "{warning}": "⚠️",
                "{check}": "✅",
                "{cross}": "❌",
                "{clock}": "⏰",
                "{link}": "🔗",
                "{moon}": "🌙",
                "{sun}": "🌅",
                "{coffee}": "☕",
                "{sleep}": "💤",
                "{fire1}": "🔥",
                "{alarm1}": "⏰",
                "{tick}": "✅",
                "{rarrow}": "➡️",
                "{bookmark}": "🔖",
                "{bell}": "🔔",
                "{specialoffer}": "🎲🎲🎲🎲🎲🎲",
                "{break_icon}": "⏸️",
                "{reload}": "🔄",
                "{party}": "🎉",
                "{money_loss}": "💸",
                "{star2}": "🌟",
            }
        }
        
        try:
            mongo_doc = self._mongo_get_doc('emoji_config')
            if mongo_doc and isinstance(mongo_doc.get('data'), dict):
                self.emoji_config = mongo_doc['data']
            elif os.path.exists(self.emoji_config_file):
                with open(self.emoji_config_file, 'r', encoding='utf-8') as f:
                    self.emoji_config = json.load(f)
                self._mongo_upsert_doc('emoji_config', self.emoji_config)
            else:
                self.emoji_config = default_emoji_config
                self.save_emoji_config()
        except Exception as e:
            logging.error(f"❌ Error loading emoji config: {e}")
            self.emoji_config = default_emoji_config
            self.save_emoji_config()
        
        self.ensure_emoji_config_keys()

    def save_emoji_config(self):
        try:
            if self._mongo_upsert_doc('emoji_config', self.emoji_config):
                logging.info("✅ Emoji configuration saved to MongoDB")
        except Exception as e:
            logging.error(f"❌ Error saving emoji config: {e}")

    def get_emoji(self, emoji_key, for_channel=False):
        try:
            if for_channel and self.use_user_account:
                return self.emoji_config['premium_emojis'].get(emoji_key, self.emoji_config['regular_emojis'].get(emoji_key, ''))
            else:
                return self.emoji_config['regular_emojis'].get(emoji_key, '')
        except KeyError:
            regular_emojis = {
                "fire": "🔥", "crown": "👑", "sparkles": "✨", "rocket": "🚀",
                "money": "💰", "chart": "📊", "target": "🎯", "trophy": "🏆",
                "gift": "🎁", "lightning": "⚡", "star": "⭐", "warning": "⚠️",
                "check": "✅", "cross": "❌", "clock": "⏰", "link": "🔗",
                "moon": "🌙", "sun": "🌅", "coffee": "☕", "sleep": "💤",
                "break_icon": "⏸️", "reload": "🔄", "party": "🎉", "money_loss": "💸", "star2": "🌟",
                "fire1": "🔥", "alarm1": "⏰", "tick": "✅", "rarrow": "➡️",
                "bookmark": "🔖",
                "bell": "🔔",
                "specialoffer": "🎲🎲🎲🎲🎲🎲",
            }
            return regular_emojis.get(emoji_key, '')

    def convert_placeholder_to_premium_emoji(self, text, for_channel=False):
        if not text:
            return text
        
        try:
            if not for_channel or not self.use_user_account:
                for placeholder, emoji in self.emoji_config.get('placeholder_to_emoji', {}).items():
                    if placeholder in text:
                        text = text.replace(placeholder, emoji)
                return text
            
            if for_channel and self.use_user_account:
                for placeholder, premium_emoji in self.emoji_config.get('premium_emojis', {}).items():
                    placeholder_format = f"{{{placeholder}}}"
                    if placeholder_format in text:
                        text = text.replace(placeholder_format, premium_emoji)
            
            for placeholder, emoji in self.emoji_config.get('placeholder_to_emoji', {}).items():
                if placeholder in text:
                    text = text.replace(placeholder, emoji)
        
        except Exception as e:
            logging.error(f"❌ Error converting placeholders: {e}")
        
        return text

    def format_with_emojis(self, text, for_channel=False):
        return self.convert_placeholder_to_premium_emoji(text, for_channel)

    def auto_detect_and_convert_message(self, message_text):
        if not message_text:
            return message_text
        
        try:
            converted_text = message_text
            for emoji, placeholder in self.emoji_config.get('emoji_to_placeholder', {}).items():
                if emoji in converted_text:
                    converted_text = converted_text.replace(emoji, placeholder)
            return converted_text
        except Exception as e:
            logging.error(f"❌ Error in auto-detect and convert: {e}")
            return message_text

    def format_custom_message_with_premium_emojis(self, text, channel_id):
        if not text:
            return text
        
        try:
            text = self.auto_detect_and_convert_message(text)
            return self.convert_placeholder_to_premium_emoji(text, for_channel=True)
        except Exception as e:
            logging.error(f"❌ Error formatting custom message: {e}")
            return text

    def ensure_emoji_config_keys(self):
        if not hasattr(self, 'emoji_config'):
            self.load_emoji_config()
        
        required_keys = ['premium_emojis', 'regular_emojis', 'emoji_to_placeholder', 'placeholder_to_emoji']
        
        for key in required_keys:
            if key not in self.emoji_config:
                if key == 'emoji_to_placeholder':
                    self.emoji_config[key] = {
                        "🔥": "{fire}",
                        "👑": "{crown}",
                        "✨": "{sparkles}",
                        "🚀": "{rocket}",
                        "💰": "{money}",
                        "📊": "{chart}",
                        "🎯": "{target}",
                        "🏆": "{trophy}",
                        "🎁": "{gift}",
                        "⚡": "{lightning}",
                        "⭐": "{star}",
                        "⚠️": "{warning}",
                        "✅": "{check}",
                "✅": "{tick}",
                        "❌": "{cross}",
                        "⏰": "{clock}",
                        "🔗": "{link}",
                        "🌙": "{moon}",
                        "🌅": "{sun}",
                        "☕": "{coffee}",
                        "💤": "{sleep}",
                "🔥": "{fire1}",
                "⏰": "{alarm1}",
                "➡️": "{rarrow}",
                        "⏸️": "{break_icon}",
                        "🔄": "{reload}",
                        "🎉": "{party}",
                        "💸": "{money_loss}",
                        "🌟": "{star2}",
                    }
                elif key == 'placeholder_to_emoji':
                    self.emoji_config[key] = {
                        "{fire}": "🔥",
                        "{crown}": "👑",
                        "{sparkles}": "✨",
                        "{rocket}": "🚀",
                        "{money}": "💰",
                        "{chart}": "📊",
                        "{target}": "🎯",
                        "{trophy}": "🏆",
                        "{gift}": "🎁",
                        "{lightning}": "⚡",
                        "{star}": "⭐",
                        "{warning}": "⚠️",
                        "{check}": "✅",
                        "{cross}": "❌",
                        "{clock}": "⏰",
                        "{link}": "🔗",
                        "{moon}": "🌙",
                        "{sun}": "🌅",
                        "{coffee}": "☕",
                        "{sleep}": "💤",
                "{fire1}": "🔥",
                "{alarm1}": "⏰",
                "{tick}": "✅",
                "{rarrow}": "➡️",
                "{bookmark}": "🔖",
                "{bell}": "🔔",
                "{specialoffer}": "🎲🎲🎲🎲🎲🎲",
                        "{break_icon}": "⏸️",
                        "{reload}": "🔄",
                        "{party}": "🎉",
                        "{money_loss}": "💸",
                        "{star2}": "🌟",
                    }
                elif key not in self.emoji_config:
                    self.emoji_config[key] = {}
        
        self.save_emoji_config()

    def initialize_configs(self):
        self.load_emoji_config()
        self.load_config()
        self.load_custom_messages()
        self.ensure_emoji_config_keys()

    def load_custom_messages(self):
        try:
            mongo_doc = self._mongo_get_doc('custom_messages')
            if mongo_doc and isinstance(mongo_doc.get('data'), dict):
                self.custom_messages = mongo_doc['data']
                logging.info(f"✅ Custom messages loaded from MongoDB")
                return

            if os.path.exists(self.custom_messages_file):
                with open(self.custom_messages_file, 'r', encoding='utf-8') as f:
                    self.custom_messages = json.load(f)
                self._mongo_upsert_doc('custom_messages', self.custom_messages)
            else:
                self.custom_messages = {}
                self.save_custom_messages()
        except Exception as e:
            logging.error(f"❌ Error loading custom messages: {e}")
            self.custom_messages = {}

    # ============= PYROGRAM USER ACCOUNT METHODS =============
    
    async def initialize_user_client(self):
        if not self.use_user_account:
            logging.warning("User account not configured. Using regular emojis.")
            return False

        async with self.user_client_lock:
            if self.user_client_initialized and self.user_app and self.user_client_connected:
                return True

            try:
                session_name = str((Path(__file__).resolve().parent / "user_session_ligas").resolve())
                
                self.user_app = Client(
                    session_name,
                    api_id=self.api_id,
                    api_hash=self.api_hash,
                    phone_number=self.phone,
                    in_memory=False,
                    sleep_threshold=30,
                    no_updates=True
                )

                await self.user_app.start()
                self.user_client_initialized = True
                self.user_client_connected = True
                
                me = await self.user_app.get_me()
                logging.info(f"✅ User account connected: {me.first_name} (ID: {me.id})")
                
                if hasattr(me, 'is_premium') and me.is_premium:
                    logging.info("✅ Premium account detected! Premium emojis will work.")

                self.user_client_keepalive_task = asyncio.create_task(self._keep_user_client_alive())
                logging.info("✅ User client keepalive task started")

                await self.resolve_all_channels()
                
                return True

            except Exception as e:
                logging.error(f"❌ Failed to initialize user account: {e}")
                self.user_client_connected = False
                self.user_client_initialized = False
                return False

    async def _keep_user_client_alive(self):
        try:
            while True:
                await asyncio.sleep(30)
                if self.user_app and self.user_client_connected:
                    try:
                        await self.user_app.get_me()
                        logging.debug("✅ User client ping successful")
                    except Exception as e:
                        logging.warning(f"⚠️ User client ping failed: {e}")
                        self.user_client_connected = False
                        await self._reconnect_user_client()
                else:
                    await self._reconnect_user_client()
        except asyncio.CancelledError:
            logging.info("🛑 User client keepalive stopped")
        except Exception as e:
            logging.error(f"❌ Keepalive error: {e}")

    async def _reconnect_user_client(self):
        try:
            if self.user_app:
                try:
                    await self.user_app.stop()
                except:
                    pass
                await asyncio.sleep(2)
                await self.user_app.start()
                self.user_client_connected = True
                logging.info("✅ User client reconnected")
        except Exception as e:
            logging.error(f"❌ Failed to reconnect user client: {e}")
            self.user_client_connected = False

    async def resolve_all_channels(self):
        if not self.user_app or not self.active_channels:
            return
        
        if self.resolution_in_progress:
            return
        
        self.resolution_in_progress = True
        logging.info("🔍 Resolving all channels...")
        
        self.username_to_id.clear()
        self.id_to_username.clear()
        self.resolved_channels.clear()
        
        for channel in self.active_channels:
            try:
                channel_str = str(channel).strip()
                
                if channel_str in self.failed_channels:
                    continue
                
                try:
                    if channel_str.startswith('@'):
                        chat = await self.user_app.get_chat(channel_str)
                        self.username_to_id[channel_str] = chat.id
                        self.id_to_username[str(chat.id)] = channel_str
                        self.resolved_channels.add(chat.id)
                        logging.info(f"✅ Resolved {channel_str} -> {chat.id}")
                    
                    elif channel_str.lstrip('-').isdigit():
                        chat_id = int(channel_str)
                        chat = await self.user_app.get_chat(chat_id)
                        self.username_to_id[channel_str] = chat_id
                        self.id_to_username[str(chat_id)] = channel_str
                        self.resolved_channels.add(chat_id)
                        logging.info(f"✅ Resolved {channel_str} -> {chat_id}")
                    
                    else:
                        logging.warning(f"⚠️ Invalid channel format: {channel_str}")
                        self.failed_channels.add(channel_str)
                        
                except (PeerIdInvalid, ChannelInvalid, ChannelPrivate, UserNotParticipant) as e:
                    logging.error(f"❌ Cannot access channel {channel_str}: {e}")
                    self.failed_channels.add(channel_str)
                except FloodWait as e:
                    logging.warning(f"⚠️ FloodWait: Waiting {e.value}s")
                    await asyncio.sleep(e.value)
                    
            except Exception as e:
                logging.error(f"❌ Failed to resolve {channel}: {e}")
                self.failed_channels.add(str(channel))
        
        logging.info(f"✅ Resolved {len(self.resolved_channels)} channel references")
        self.resolution_in_progress = False

    async def get_chat_id(self, channel_identifier):
        if not self.user_app:
            return None
        
        identifier = str(channel_identifier).strip()
        
        if identifier in self.username_to_id:
            return self.username_to_id[identifier]
        
        if identifier.lstrip('-').isdigit():
            chat_id = int(identifier)
            if chat_id in self.id_to_username:
                return chat_id
        
        try:
            if identifier.startswith('@'):
                chat = await self.user_app.get_chat(identifier)
                self.username_to_id[identifier] = chat.id
                self.id_to_username[str(chat.id)] = identifier
                return chat.id
            elif identifier.lstrip('-').isdigit():
                chat_id = int(identifier)
                chat = await self.user_app.get_chat(chat_id)
                self.username_to_id[identifier] = chat_id
                self.id_to_username[str(chat_id)] = identifier
                return chat_id
        except Exception as e:
            logging.error(f"❌ Failed to resolve {identifier}: {e}")
            self.failed_channels.add(identifier)
        
        return None

    # ============= COMMAND HANDLERS =============
    
    async def start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_user.id not in self.config['admin_ids']:
            await update.message.reply_text("Access denied contact admin @aviii56")
            return
            
        await update.message.reply_text(
            "🤖 WinGo Bot Admin Panel\n\n"
            "🎯 REAL AI PATTERN RECOGNITION\n"
            "• GPT-4/Claude like pattern learning\n"
            "• Win Rate: 80-85%+ target\n"
            "• Learns from every result\n\n"
            "⏰ SCHEDULE:\n"
            "• Custom schedule per channel available\n"
            "• Morning Message: 5:00 AM\n"
            "• Night Message: 12:00 AM\n\n"
            "Select an option below:",
            reply_markup=self.get_keyboard('main')
        )

    async def handle_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query
        await query.answer()
        
        if query.from_user.id not in self.config['admin_ids']:
            await query.edit_message_text("Not authorized")
            return
            
        data = query.data
        chat_id = query.message.chat_id
        
        try:
            if data == 'main_menu':
                await query.edit_message_text(
                    "🤖 WinGo Bot Admin Panel\n\n"
                    "🎯 REAL AI PATTERN RECOGNITION\n"
                    "• GPT-4/Claude like pattern learning\n"
                    "• Win Rate: 80-85%+ target\n"
                    "• Learns from every result\n\n"
                    "⏰ SCHEDULE:\n"
                    "• Custom schedule per channel available\n"
                    "• Morning Message: 5:00 AM\n"
                    "• Night Message: 12:00 AM\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('main')
                )
                
            elif data == 'stats':
                data_fetch = await self.fetch_live_data()
                if data_fetch and self.waiting_for_result:
                    await self.check_result_and_send_next(context, data_fetch)
                
                total_predictions = self.session_wins + self.session_losses
                session_win_rate = (self.session_wins / total_predictions * 100) if total_predictions > 0 else 0
                
                # Count active channels based on custom schedules
                active_now_count = 0
                for channel in self.active_channels:
                    if self.is_channel_active(channel):
                        active_now_count += 1
                
                stats_text = f"""📊 Bot Statistics & AI Analysis

🤖 AI SYSTEM:
• AI Accuracy: {self.ai_accuracy:.2%}
• AI Predictions: {self.ai_total_predictions}
• AI Correct: {self.ai_correct_predictions}
• Learning Cycles: {self.ai_learning_cycles}
• Patterns Learned: {len(self.pattern_database)}

📈 PERFORMANCE:
• Session: {self.session_wins}W {self.session_losses}L
• Win Rate: {session_win_rate:.1f}%
• Consecutive Wins: {self.consecutive_wins}
• Consecutive Losses: {self.consecutive_losses}

🌐 CHANNELS:
• Total Channels: {len(self.active_channels)}
• Currently Active: {active_now_count}
• With Custom Schedule: {len(self.channel_custom_schedules)}
• Paused: {sum(1 for c in self.active_channels if not self.is_channel_prediction_active(c))}

🕒 SYSTEM:
• User Account: {'🟢 Active' if self.use_user_account and self.user_client_connected else '🔴 Inactive'}
• AI Status: {'🟢 Learning' if self.ai_total_predictions > 0 else '🟡 Training'}"""
                
                await query.edit_message_text(stats_text, reply_markup=self.get_keyboard('main'))
                
            elif data == 'templates_main_menu':
                await query.edit_message_text(
                    "📝 Templates Management\n\n"
                    "Edit message templates.\n"
                    "Use {{placeholders}} for dynamic content.\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('templates_main_menu')
                )
                
            elif data == 'edit_all_templates':
                await query.edit_message_text(
                    "📄 Select template to edit for ALL channels:",
                    reply_markup=self.get_keyboard('edit_all_templates')
                )
                
            elif data == 'select_channel_templates':
                await query.edit_message_text(
                    "📢 Select channel to edit templates:",
                    reply_markup=self.get_keyboard('select_channel_templates')
                )
                
            elif data.startswith('channel_templates:'):
                channel_id = data.split(':', 1)[1]
                await query.edit_message_text(
                    f"📝 Templates for {channel_id}\n\nSelect template to edit:",
                    reply_markup=self.get_keyboard('channel_templates', channel_id)
                )
                
            elif data.startswith('edit_template:'):
                parts = data.split(':')
                channel_id = parts[1]
                template_key = parts[2]
                
                if channel_id == 'all':
                    self.user_state[chat_id] = f'awaiting_template_all:{template_key}'
                    await query.edit_message_text(
                        f"📝 Edit Template for ALL Channels\n\n"
                        f"Template: {template_key}\n\n"
                        f"Send new template:",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="templates_main_menu")]])
                    )
                else:
                    self.user_state[chat_id] = f'awaiting_template:{channel_id}:{template_key}'
                    await query.edit_message_text(
                        f"📝 Edit Template for {channel_id}\n\n"
                        f"Template: {template_key}\n\n"
                        f"Send new template:",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"channel_templates:{channel_id}")]])
                    )
            
            elif data == 'event_media_menu':
                await query.edit_message_text(
                    "📝 Event Media System\n\n"
                    "Set media for each event type:\n"
                    "• Session Start\n"
                    "• Break\n"
                    "• Good Morning\n"
                    "• Good Night\n"
                    "• Win Result\n"
                    "• Loss Result\n\n"
                    "Each event can have multiple media files.\n"
                    "You can view, add, and delete media.",
                    reply_markup=self.get_keyboard('event_media_menu')
                )

            elif data == 'select_channel_event_media':
                await query.edit_message_text(
                    "📋 Select Channel for Event Media:",
                    reply_markup=self.get_keyboard('select_channel_event_media')
                )
                
            elif data.startswith('event_media_channel:'):
                channel_id = data.split(':', 1)[1]
                
                # Build keyboard with counts
                media_menu = []
                events = list(self.message_types.items())
                for i in range(0, len(events), 2):
                    key1, name1 = events[i]
                    count1 = len(self.get_event_media(channel_id, key1))
                    
                    if i+1 < len(events):
                        key2, name2 = events[i+1]
                        count2 = len(self.get_event_media(channel_id, key2))
                        row = [
                            InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"event_media_type:{channel_id}:{key1}"),
                            InlineKeyboardButton(f"{name2} ({count2})", callback_data=f"event_media_type:{channel_id}:{key2}")
                        ]
                    else:
                        row = [InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"event_media_type:{channel_id}:{key1}")]
                    media_menu.append(row)
                media_menu.append([InlineKeyboardButton("🔙 Back", callback_data="select_channel_event_media")])
                
                await query.edit_message_text(
                    f"📝 Event Media for {channel_id}\n\nSelect event type to configure:",
                    reply_markup=InlineKeyboardMarkup(media_menu)
                )
                
            elif data.startswith('event_media_type:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                media_list = self.get_event_media(channel_id, event_type)
                media_count = len(media_list)
                event_name = self.message_types.get(event_type, event_type)
                
                media_type_menu = [
                    [InlineKeyboardButton(f"➕ Add {event_name} Media", callback_data=f"add_event_media:{channel_id}:{event_type}")],
                ]
                
                if media_count > 0:
                    media_type_menu.append([
                        InlineKeyboardButton(f"👁️ View All ({media_count})", callback_data=f"view_event_media:{channel_id}:{event_type}"),
                        InlineKeyboardButton(f"🗑️ Delete All", callback_data=f"delete_all_event_media:{channel_id}:{event_type}")
                    ])
                
                media_type_menu.append([InlineKeyboardButton("🔙 Back", callback_data=f"event_media_channel:{channel_id}")])
                
                await query.edit_message_text(
                    f"{event_name} Media for {channel_id}\n\nCurrent: {media_count} files",
                    reply_markup=InlineKeyboardMarkup(media_type_menu)
                )
                
            elif data.startswith('add_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                self.user_state[chat_id] = f'awaiting_event_media:{channel_id}:{event_type}'
                
                await query.edit_message_text(
                    f"➕ Add {self.message_types.get(event_type, event_type)} Media for {channel_id}\n\n"
                    f"Send photos, videos, GIFs, stickers, or ANY file type.\n"
                    f"You can send multiple files.\n\n"
                    f"Send files now (multiple allowed).\n"
                    f"Type /done when finished:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"event_media_type:{channel_id}:{event_type}")]])
                )
                
            elif data.startswith('view_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                media_list = self.get_event_media(channel_id, event_type)
                if not media_list:
                    await query.edit_message_text(
                        f"❌ No {self.message_types.get(event_type, event_type)} media for {channel_id}",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                    return
                
                text = f"👁️ {self.message_types.get(event_type, event_type)} Media for {channel_id}\n\n"
                for i, media in enumerate(media_list):
                    media_type = media.get('type', 'unknown')
                    file_name = media.get('file_name', f'File {i+1}')
                    text += f"{i+1}. {media_type.upper()}: {file_name}\n"
                
                buttons = []
                for i in range(len(media_list)):
                    buttons.append([InlineKeyboardButton(f"🗑️ Delete {i+1}", callback_data=f"delete_event_media:{channel_id}:{event_type}:{i}")])
                buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"event_media_type:{channel_id}:{event_type}")])
                
                await query.edit_message_text(
                    text,
                    reply_markup=InlineKeyboardMarkup(buttons)
                )
                
            elif data.startswith('delete_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                index = int(parts[3])
                
                if self.delete_event_media(channel_id, event_type, index):
                    await query.edit_message_text(
                        f"✅ Deleted {self.message_types.get(event_type, event_type)} media #{index+1}",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                    
            elif data.startswith('delete_all_event_media:'):
                parts = data.split(':')
                channel_id = parts[1]
                event_type = parts[2]
                
                if self.delete_event_media(channel_id, event_type):
                    await query.edit_message_text(
                        f"✅ All {self.message_types.get(event_type, event_type)} media deleted",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                else:
                    await query.edit_message_text(
                        f"❌ Failed to delete",
                        reply_markup=self.get_keyboard('event_media_type', channel_id, event_type=event_type)
                    )
                    
            elif data == 'custom_messages_menu':
                await query.edit_message_text(
                    "🎯 Custom Messages System\n\n"
                    "Create messages exactly as you want them to appear.\n"
                    "Send a message with media + text combined.\n"
                    "Bot will store and forward it exactly as sent.\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('custom_messages_menu')
                )
                
            elif data == 'select_channel_custom_messages':
                await query.edit_message_text(
                    "📋 Select Channel for Custom Messages:",
                    reply_markup=self.get_keyboard('select_channel_custom_messages')
                )
                
            elif data.startswith('custom_messages_channel:'):
                channel_id = data.split(':', 1)[1]
                await query.edit_message_text(
                    f"🎯 Custom Messages for {channel_id}\n\n"
                    f"Select message type to configure:",
                    reply_markup=self.get_keyboard('custom_messages_channel', channel_id)
                )
                
            elif data.startswith('custom_messages_type:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                
                await query.edit_message_text(
                    f"{self.message_types.get(msg_type, msg_type)} Custom Messages for {channel_id}",
                    reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                )
                
            elif data.startswith('add_custom_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2] if len(parts) > 2 else None
                
                if msg_type:
                    self.user_state[chat_id] = f'awaiting_custom_message:{channel_id}:{msg_type}'
                    await query.edit_message_text(
                        f"📝 Send the message EXACTLY as you want it to appear.\n\n"
                        f"• Text only, media only, or media+text together\n"
                        f"• Bot will store and forward exactly as sent\n\n"
                        f"Type /cancel to abort.",
                        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_messages_type:{channel_id}:{msg_type}")]])
                    )
                else:
                    await query.edit_message_text(
                        f"➕ Add Custom Message for {channel_id}\n\n"
                        f"Select message type:",
                        reply_markup=self.get_message_type_keyboard(channel_id)
                    )
                    
            elif data.startswith('view_custom_messages:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if not messages:
                    await query.edit_message_text(
                        f"❌ No {self.message_types.get(msg_type, msg_type)} messages for {channel_id}",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                    return
                
                text = f"👁️ {self.message_types.get(msg_type, msg_type)} Messages for {channel_id}\n\n"
                for i, msg in enumerate(messages):
                    media_count = len(msg.get('media_group', []))
                    text_len = len(msg.get('text', ''))
                    send_order = msg.get('send_order', 'text_first')
                    text += f"{i+1}. {media_count} media, {text_len} chars, {send_order}\n"
                
                buttons = []
                for i in range(len(messages)):
                    buttons.append([InlineKeyboardButton(f"✏️ Edit {i+1}", callback_data=f"edit_custom_message:{channel_id}:{msg_type}:{i}")])
                buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"custom_messages_type:{channel_id}:{msg_type}")])
                
                await query.edit_message_text(text, reply_markup=InlineKeyboardMarkup(buttons))
                
            elif data.startswith('edit_custom_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                await query.edit_message_text(
                    f"✏️ Edit Message #{msg_index+1}",
                    reply_markup=self.get_keyboard('edit_custom_message', channel_id, event_type=msg_type, message_index=msg_index)
                )
                
            elif data.startswith('preview_custom:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if messages and msg_index < len(messages):
                    message_data = messages[msg_index]
                    media_count = len(message_data.get('media_group', []))
                    text_len = len(message_data.get('text', ''))
                    send_order = message_data.get('send_order', 'text_first')
                    
                    preview_text = f"""👁️ Message Preview

• Media Items: {media_count}
• Text Length: {text_len} chars
• Send Order: {send_order}

Would you like to test send this message?"""
                    
                    await query.edit_message_text(
                        preview_text,
                        reply_markup=InlineKeyboardMarkup([
                            [InlineKeyboardButton("🚀 Test Send", callback_data=f"test_send_custom:{channel_id}:{msg_type}:{msg_index}"),
                             InlineKeyboardButton("🔙 Back", callback_data=f"edit_custom_message:{channel_id}:{msg_type}:{msg_index}")]
                        ])
                    )
                    
            elif data.startswith('test_send_custom:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if messages and msg_index < len(messages):
                    await query.edit_message_text("🚀 Sending test message...")
                    await self.send_stored_message(context, channel_id, messages[msg_index])
                    await query.edit_message_text(
                        f"✅ Test message sent to {channel_id}!",
                        reply_markup=self.get_keyboard('edit_custom_message', channel_id, event_type=msg_type, message_index=msg_index)
                    )
                    
            elif data.startswith('change_custom_order:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                await query.edit_message_text(
                    f"🔄 Select Send Order for Message #{msg_index+1}:",
                    reply_markup=self.get_keyboard('send_order_menu', channel_id, event_type=msg_type, message_index=msg_index)
                )
                
            elif data.startswith('set_custom_order:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                send_order = parts[4]
                
                messages = self.get_custom_messages(channel_id, msg_type)
                if messages and msg_index < len(messages):
                    messages[msg_index]['send_order'] = send_order
                    self.save_custom_messages()
                    await query.edit_message_text(
                        f"✅ Send order set to {send_order}!",
                        reply_markup=self.get_keyboard('edit_custom_message', channel_id, event_type=msg_type, message_index=msg_index)
                    )
                    
            elif data.startswith('delete_custom_message:'):
                parts = data.split(':')
                channel_id = parts[1]
                msg_type = parts[2]
                msg_index = int(parts[3])
                
                if self.delete_custom_message(channel_id, msg_type, msg_index):
                    await query.edit_message_text(
                        f"✅ Custom message deleted!",
                        reply_markup=self.get_keyboard('custom_messages_type', channel_id, event_type=msg_type)
                    )
                    
            elif data == 'break_duration_menu':
                await query.edit_message_text(
                    f"⏱️ Break Duration Settings\n\n"
                    f"Current break duration: {self.custom_break_duration} minutes\n\n"
                    f"Set how long the break should last (1-120 minutes).",
                    reply_markup=self.get_keyboard('break_duration_menu')
                )
                
            elif data == 'set_break_duration':
                self.user_state[chat_id] = 'awaiting_break_duration'
                await query.edit_message_text(
                    f"⏱️ Set Break Duration\n\n"
                    f"Current: {self.custom_break_duration} minutes\n\n"
                    f"Enter new break duration in minutes (1-120):",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="break_duration_menu")]])
                )
            
            elif data == 'ai_management':
                await query.edit_message_text(
                    "🤖 AI Pattern Recognition Management\n\n"
                    f"Current AI Accuracy: {self.ai_accuracy:.2%}\n"
                    f"Patterns Learned: {len(self.pattern_database)}\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'ai_stats':
                stats_text = f"""🤖 AI PATTERN RECOGNITION STATISTICS

📊 ACCURACY:
• Overall Accuracy: {self.ai_accuracy:.2%}
• Total Predictions: {self.ai_total_predictions}
• Correct Predictions: {self.ai_correct_predictions}
• Learning Cycles: {self.ai_learning_cycles}

🧠 PATTERN DATABASE:
• Patterns Learned: {len(self.pattern_database)}
• Pattern Types: {sum(1 for v in self.pattern_types.values() if v > 0)}

📈 PERFORMANCE TRENDS:
• Current Confidence: {getattr(self, 'last_ai_confidence', 0)*100:.1f}%
• Recent Success Rate: {(sum(1 for h in self.ai_prediction_history[-20:] if h.get('was_correct'))/20*100 if len(self.ai_prediction_history) >= 20 else 0):.1f}%

🔍 PATTERN ANALYSIS:
• Alternating Patterns: {self.pattern_types['alternating']}
• Streak Patterns: {self.pattern_types['streak']}
• Zigzag Patterns: {self.pattern_types['zigzag']}
• Cluster Patterns: {self.pattern_types['cluster']}"""
                
                await query.edit_message_text(stats_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'view_patterns':
                if not self.pattern_database:
                    await query.edit_message_text(
                        "❌ No patterns learned yet!",
                        reply_markup=self.get_keyboard('ai_management')
                    )
                    return
                
                patterns_text = "🔍 TOP WINNING PATTERNS:\n\n"
                sorted_patterns = sorted(
                    self.pattern_database.items(),
                    key=lambda x: x[1].get('success_rate', 0),
                    reverse=True
                )[:10]
                
                for i, (pattern_hash, pattern_data) in enumerate(sorted_patterns):
                    success_rate = pattern_data.get('success_rate', 0) * 100
                    occurrences = pattern_data.get('total_occurrences', 0)
                    patterns_text += f"{i+1}. Success: {success_rate:.1f}% ({occurrences} times)\n"
                    patterns_text += f"   Hash: {pattern_hash[:8]}...\n\n"
                
                await query.edit_message_text(patterns_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'retrain_ai':
                await query.edit_message_text("🔄 Retraining AI model...")
                self.retrain_ai_model()
                await query.edit_message_text(
                    f"✅ AI Model retrained!\nAccuracy: {self.ai_accuracy:.2%}",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'clear_ai_data':
                confirm_keyboard = InlineKeyboardMarkup([
                    [InlineKeyboardButton("✅ Yes, Clear All", callback_data="confirm_clear_ai_data"),
                     InlineKeyboardButton("❌ No, Keep Data", callback_data="ai_management")]
                ])
                await query.edit_message_text(
                    "⚠️ WARNING: Clear ALL AI Learning Data?\n\n"
                    "This action cannot be undone!",
                    reply_markup=confirm_keyboard
                )
                
            elif data == 'confirm_clear_ai_data':
                self.pattern_database = {}
                self.ai_correct_predictions = 0
                self.ai_total_predictions = 0
                self.ai_accuracy = 0.0
                self.ai_learning_cycles = 0
                self.pattern_history = []
                self.ai_prediction_history.clear()
                self.save_ai_model()
                
                await query.edit_message_text(
                    "✅ All AI data cleared!",
                    reply_markup=self.get_keyboard('ai_management')
                )
                
            elif data == 'pattern_analysis':
                if not self.ai_prediction_history:
                    await query.edit_message_text(
                        "❌ No prediction history yet!",
                        reply_markup=self.get_keyboard('ai_management')
                    )
                    return
                
                recent_history = list(self.ai_prediction_history)[-20:]
                correct = sum(1 for h in recent_history if h.get('was_correct'))
                total = len(recent_history)
                recent_accuracy = (correct / total * 100) if total > 0 else 0
                
                analysis_text = f"""🎯 PATTERN ANALYSIS

📊 RECENT PERFORMANCE (Last 20):
• Accuracy: {recent_accuracy:.1f}%
• Correct: {correct}/{total}

⚡ PREDICTION CONFIDENCE:
• Current: {getattr(self, 'last_ai_confidence', 0)*100:.1f}%
• Threshold: {self.ai_confidence_threshold*100:.0f}%

🔮 RECOMMENDATION:
• {'✅ AI is performing well' if recent_accuracy > 65 else '⚠️ AI needs more training'}"""
                
                await query.edit_message_text(analysis_text, reply_markup=self.get_keyboard('ai_management'))
                
            elif data == 'prediction_control':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                    
                await query.edit_message_text(
                    "⏯️ Prediction Control\n\n"
                    "• 🟢 = Active\n"
                    "• ⏸️ = Paused\n\n"
                    "Select channel to toggle:",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data.startswith('toggle_channel_prediction:'):
                channel_id = data.split(':', 1)[1]
                new_status = self.toggle_channel_prediction(channel_id)
                status_text = "🟢 ACTIVATED" if new_status else "⏸️ PAUSED"
                
                await query.edit_message_text(
                    f"✅ Predictions {status_text} for {channel_id}",
                    reply_markup=self.get_keyboard('prediction_control')
                )
                
            elif data == 'start_all_predictions':
                for channel_id in self.active_channels:
                    self.set_channel_prediction_status(channel_id, True)
                await query.edit_message_text("✅ All channel predictions STARTED!", reply_markup=self.get_keyboard('prediction_control'))
                
            elif data == 'pause_all_predictions':
                for channel_id in self.active_channels:
                    self.set_channel_prediction_status(channel_id, False)
                await query.edit_message_text("⏸️ All channel predictions PAUSED!", reply_markup=self.get_keyboard('prediction_control'))
                
            elif data == 'schedule_menu':
                await query.edit_message_text(
                    "⏰ Schedule Management\n\n"
                    "Set custom prediction times for each channel.\n"
                    "Format: HH:MM-HH:MM (24-hour format)\n"
                    "Example: 10:00-11:00\n\n"
                    "Select an option:",
                    reply_markup=self.get_keyboard('schedule_menu')
                )
                
            elif data == 'select_channel_schedule':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                await query.edit_message_text(
                    "📢 Select a channel to configure schedule:",
                    reply_markup=self.get_keyboard('select_channel_schedule')
                )
                
            elif data.startswith('channel_schedule:'):
                channel_id = data.split(':', 1)[1]
                schedule_display = self.get_channel_schedule_display(channel_id)
                
                await query.edit_message_text(
                    f"⏰ Schedule for {channel_id}\n\n"
                    f"Current Schedule:\n{schedule_display}\n\n"
                    f"Select an action:",
                    reply_markup=self.get_keyboard('channel_schedule', channel_id)
                )
                
            elif data.startswith('add_schedule_slot:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_schedule_slot:{channel_id}'
                await query.edit_message_text(
                    f"➕ Add Schedule Slot for {channel_id}\n\n"
                    f"Send the schedule slot in format:\n"
                    f"HH:MM-HH:MM (24-hour format)\n\n"
                    f"Examples:\n"
                    f"10:00-11:00\n"
                    f"14:00-15:00\n"
                    f"17:00-18:00\n"
                    f"20:00-21:00\n\n"
                    f"Type /cancel to abort.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"channel_schedule:{channel_id}")]])
                )
                
            elif data.startswith('remove_schedule_slot:'):
                channel_id = data.split(':', 1)[1]
                if channel_id in self.channel_custom_schedules and self.channel_custom_schedules[channel_id]:
                    buttons = []
                    for i, slot in enumerate(self.channel_custom_schedules[channel_id]):
                        try:
                            start, end = slot.split('-')
                            start_12h = self.format_time_str_12h(start)
                            end_12h = self.format_time_str_12h(end)
                            display = f"{start_12h} - {end_12h}"
                        except:
                            display = slot
                        buttons.append([InlineKeyboardButton(f"❌ Remove {display}", callback_data=f"confirm_remove_slot:{channel_id}:{i}")])
                    buttons.append([InlineKeyboardButton("🔙 Back", callback_data=f"channel_schedule:{channel_id}")])
                    await query.edit_message_text(
                        f"Select slot to remove:",
                        reply_markup=InlineKeyboardMarkup(buttons)
                    )
                else:
                    await query.edit_message_text(
                        "❌ No custom schedule slots to remove!",
                        reply_markup=self.get_keyboard('channel_schedule', channel_id)
                    )
                    
            elif data.startswith('confirm_remove_slot:'):
                parts = data.split(':')
                channel_id = parts[1]
                index = int(parts[2])
                if self.remove_channel_schedule_slot(channel_id, index):
                    await query.edit_message_text(
                        "✅ Schedule slot removed!",
                        reply_markup=self.get_keyboard('channel_schedule', channel_id)
                    )
                else:
                    await query.edit_message_text(
                        "❌ Failed to remove slot!",
                        reply_markup=self.get_keyboard('channel_schedule', channel_id)
                    )
                    
            elif data.startswith('clear_schedule:'):
                channel_id = data.split(':', 1)[1]
                if self.clear_channel_custom_schedule(channel_id):
                    await query.edit_message_text(
                        "✅ All schedule slots cleared! Using global schedule.",
                        reply_markup=self.get_keyboard('channel_schedule', channel_id)
                    )
                else:
                    await query.edit_message_text(
                        "❌ No custom schedule to clear!",
                        reply_markup=self.get_keyboard('channel_schedule', channel_id)
                    )
                    
            elif data == 'select_channel_config':
                if not self.active_channels:
                    await query.edit_message_text(
                        "❌ No channels added yet!",
                        reply_markup=self.get_keyboard('main')
                    )
                    return
                await query.edit_message_text("📢 Select a channel to configure:", reply_markup=self.get_keyboard('select_channel'))
                
            elif data.startswith('channel_config:'):
                channel_id = data.split(':', 1)[1]
                channel_status = self.is_channel_prediction_active(channel_id)
                status_text = "🟢 ACTIVE" if channel_status else "⏸️ PAUSED"
                
                schedule_display = self.get_channel_schedule_display(channel_id)
                is_active = self.is_channel_active(channel_id)
                
                config_text = f"""⚙️ Configuration for {channel_id}

🎯 AI Accuracy: {self.ai_accuracy:.2%}

Prediction Status: {status_text}
Current Time: {self.get_ist_now().strftime('%I:%M %p')}
Channel Active: {'🟢 YES' if is_active else '⏸️ NO'}

Schedule:
{schedule_display[:200]}

Select what to configure:"""
                
                await query.edit_message_text(config_text, reply_markup=self.get_keyboard('channel_config', channel_id))
                
            elif data.startswith('links_setup:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                
                links_text = f"""🔗 Links Setup for {channel_id}

• Register Link: {channel_config['register_link']}
• Promo Text: {channel_config['promotional_text'][:50]}...

Select what to change:"""
                
                await query.edit_message_text(links_text, reply_markup=self.get_keyboard('links_setup', channel_id))
                
            elif data.startswith('toggle_links:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                channel_config['show_links'] = not channel_config['show_links']
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['show_links'] else "disabled"
                await query.edit_message_text(f"✅ Links display {status}", reply_markup=self.get_keyboard('links_setup', channel_id))
                
            elif data.startswith('toggle_promo:'):
                channel_id = data.split(':', 1)[1]
                channel_config = self.get_channel_config(channel_id)
                channel_config['show_promo'] = not channel_config['show_promo']
                self.update_channel_config(channel_id, channel_config)
                
                status = "enabled" if channel_config['show_promo'] else "disabled"
                await query.edit_message_text(f"✅ Promo text display {status}", reply_markup=self.get_keyboard('links_setup', channel_id))
                
            elif data.startswith('change_register_link:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_register_link:{channel_id}'
                await query.edit_message_text(
                    f"✏️ Change Register Link for {channel_id}\n\nSend the new register link:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"links_setup:{channel_id}")]])
                )
                
            elif data.startswith('change_promo_text:'):
                channel_id = data.split(':', 1)[1]
                self.user_state[chat_id] = f'awaiting_promo_text:{channel_id}'
                await query.edit_message_text(
                    f"📢 Change Promo Text for {channel_id}\n\nSend the new promotional text:",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data=f"links_setup:{channel_id}")]])
                )
                
            elif data == 'add_channel':
                self.user_state[chat_id] = 'awaiting_add_channel'
                await query.edit_message_text(
                    "➕ Add New Channel\n\n"
                    "Send channel username (@mychannel) or numeric ID (-1001234567890):\n\n"
                    "Bot must be member of the channel.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="main_menu")]])
                )
                
            elif data == 'remove_channel':
                if not self.active_channels:
                    await query.edit_message_text("❌ No channels to remove!", reply_markup=self.get_keyboard('main'))
                    return
                await query.edit_message_text("🗑️ Remove Channel\n\nSelect channel to remove:", reply_markup=self.get_keyboard('remove_channel'))
                
            elif data.startswith('remove_channel_confirm:'):
                channel_id = data.split(':', 1)[1]
                if channel_id in self.active_channels:
                    self.active_channels.remove(channel_id)
                    if channel_id in self.channel_configs:
                        del self.channel_configs[channel_id]
                    if channel_id in self.channel_prediction_status:
                        del self.channel_prediction_status[channel_id]
                    if channel_id in self.channel_custom_schedules:
                        del self.channel_custom_schedules[channel_id]
                    self.save_config()
                    await query.edit_message_text(f"✅ Channel {channel_id} removed successfully!", reply_markup=self.get_keyboard('main'))
                else:
                    await query.edit_message_text(f"❌ Channel {channel_id} not found!", reply_markup=self.get_keyboard('main'))
                
            elif data == 'broadcast_all':
                self.user_state[chat_id] = 'awaiting_broadcast_all'
                await query.edit_message_text(
                    "📢 Broadcast to All Active Channels\n\n"
                    "Send the message text now.\n"
                    "Use /cancel to abort.",
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="main_menu")]])
                )

            elif data == 'advanced':
                await query.edit_message_text("🔄 Advanced Options", reply_markup=self.get_keyboard('advanced'))
                
            elif data == 'reset_table':
                self.session_predictions = []
                self.consecutive_losses = 0
                self.consecutive_wins = 0
                self.session_wins = 0
                self.session_losses = 0
                self.predictions = {}
                self.waiting_for_result = False
                self.break_message_sent = False
                self.last_result_was_win = False
                self.big_small_history.clear()
                await query.edit_message_text("✅ Session reset complete!", reply_markup=self.get_keyboard('advanced'))
                
            elif data == 'restart_bot':
                await query.edit_message_text("🔄 Restarting bot...")
                if self.user_app and self.use_user_account and self.user_client_connected:
                    await self.user_app.stop()
                raise SystemExit(1)
                
            elif data == 'resolve_peers':
                if self.use_user_account and self.user_app:
                    await query.edit_message_text("🔍 Resolving peers...")
                    await self.resolve_all_channels()
                    await query.edit_message_text("✅ Peers resolved successfully!", reply_markup=self.get_keyboard('advanced'))
                else:
                    await query.edit_message_text("❌ User account not active", reply_markup=self.get_keyboard('advanced'))
                
        except Exception as e:
            logging.error(f"Callback error: {e}")
            await query.edit_message_text(f"❌ Error: {str(e)}", reply_markup=self.get_keyboard('main'))

    async def handle_message(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_user is None or update.effective_user.id not in self.config['admin_ids']:
            return
            
        chat_id = update.effective_chat.id
        message = update.message
        
        if chat_id not in self.user_state:
            return
            
        state = self.user_state[chat_id]
        text = message.text.strip() if message.text else ""
        
        if text == '/cancel':
            self.user_state.pop(chat_id, None)
            await message.reply_text("❌ Operation cancelled.")
            return
        
        if state == 'awaiting_broadcast_all' and text:
            sent = 0
            failed = 0
            for channel in self.active_channels:
                try:
                    if not self.is_channel_subscription_active(channel):
                        continue
                    ok = await self.send_message_with_retry(
                        context=context,
                        chat_id=channel,
                        text=text,
                        for_channel=True
                    )
                    if ok:
                        sent += 1
                    else:
                        failed += 1
                except Exception:
                    failed += 1

            await message.reply_text(f"✅ Broadcast complete\n• Sent: {sent}\n• Failed: {failed}")
            del self.user_state[chat_id]
            return

        elif state == 'awaiting_add_channel' and text:
            channel = text.strip()
            if channel.startswith('@') or channel.startswith('-100'):
                if channel not in self.active_channels:
                    self.active_channels.append(channel)
                    if channel not in self.channel_configs:
                        self.channel_configs[channel] = {
                            'register_link': "https://bdgsg.com//#/register?invitationCode=5151329947",
                            'promotional_text': "🎁 Register now and get DAILY FREE GIFT CODE! 🎁",
                            'show_links': True,
                            'show_promo': True,
                            'templates': self.default_templates.copy()
                        }
                    self.channel_prediction_status[channel] = True
                    self.save_config()
                    self.user_state[chat_id] = f'awaiting_subscription_days:{channel}'
                    await message.reply_text(
                        f"✅ Channel {channel} added and enabled.\n\n"
                        f"Now send subscription days for this channel (example: 30)."
                    )
                    return
                else:
                    await message.reply_text("❌ Channel already exists!")
            else:
                await message.reply_text("❌ Invalid format! Use @username or -100... ID")
            del self.user_state[chat_id]

        elif state.startswith('awaiting_subscription_days:') and text:
            channel_id = state.split(':', 1)[1]
            try:
                days = int(text.strip())
                if days < 1 or days > 3650:
                    await message.reply_text("❌ Enter valid days between 1 and 3650")
                else:
                    sub = self.set_channel_subscription_days(channel_id, days)
                    await message.reply_text(
                        f"✅ Subscription set for {channel_id}\n"
                        f"Days: {days}\n"
                        f"Expires: {sub.get('expires_at')}"
                    )
            except Exception:
                await message.reply_text("❌ Invalid number. Send days like: 30")
            del self.user_state[chat_id]

        elif state == 'awaiting_break_duration' and text:
            try:
                duration = int(text)
                if 1 <= duration <= 120:
                    self.custom_break_duration = duration
                    self.save_config()
                    await message.reply_text(f"✅ Break duration set to {duration} minutes!")
                else:
                    await message.reply_text("❌ Duration must be between 1 and 120 minutes!")
            except ValueError:
                await message.reply_text("❌ Please enter a valid number!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_schedule_slot:') and text:
            channel_id = state.split(':', 1)[1]
            # Validate slot format HH:MM-HH:MM
            if re.match(r'^([0-1]?[0-9]|2[0-3]):[0-5][0-9]-([0-1]?[0-9]|2[0-3]):[0-5][0-9]$', text):
                start, end = text.split('-')
                start_hour, start_min = map(int, start.split(':'))
                end_hour, end_min = map(int, end.split(':'))
                start_time = start_hour * 60 + start_min
                end_time = end_hour * 60 + end_min
                if start_time < end_time:
                    if self.add_channel_schedule_slot(channel_id, start, end):
                        await message.reply_text(f"✅ Schedule slot {text} added for {channel_id}!")
                    else:
                        await message.reply_text(f"❌ Schedule slot already exists!")
                else:
                    await message.reply_text("❌ End time must be after start time!")
            else:
                await message.reply_text("❌ Invalid format! Use HH:MM-HH:MM (24-hour format)")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_template:') and text:
            parts = state.split(':')
            channel_id = parts[1]
            template_key = parts[2]
            self.update_channel_config(channel_id, {'templates': {template_key: text}})
            await message.reply_text(f"✅ Template updated for {channel_id}!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_template_all:') and text:
            template_key = state.split(':', 1)[1]
            for channel_id in self.active_channels:
                self.update_channel_config(channel_id, {'templates': {template_key: text}})
            await message.reply_text(f"✅ Template updated for ALL channels!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_custom_message:') and (message.photo or message.video or message.document or message.animation or message.sticker or text):
            parts = state.split(':')
            channel_id = parts[1]
            msg_type = parts[2]
            
            message_data = {
                'media_group': [],
                'text': '',
                'send_order': 'text_first',
                'timestamp': datetime.now().isoformat(),
                'source_chat_id': message.chat_id,
                'source_message_id': message.message_id
            }
            
            media_items = []
            
            if message.photo:
                media_items.append({
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif message.video:
                media_items.append({
                    'type': 'video',
                    'file_id': message.video.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif message.animation:
                media_items.append({
                    'type': 'animation',
                    'file_id': message.animation.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif message.sticker:
                media_items.append({
                    'type': 'sticker',
                    'file_id': message.sticker.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                detected_type, actual_type = self.detect_media_type_from_file(file_name, mime_type)
                media_items.append({
                    'type': actual_type,
                    'file_id': message.document.file_id,
                    'file_name': file_name,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                })
                if message.caption:
                    message_data['text'] = self.auto_detect_and_convert_message(message.caption)
                    
            elif text:
                message_data['text'] = self.auto_detect_and_convert_message(text)
                
            message_data['media_group'] = media_items
            
            if media_items and message_data['text']:
                message_data['send_order'] = 'combined'
            elif media_items:
                message_data['send_order'] = 'media_first'
            else:
                message_data['send_order'] = 'text_first'
            
            index = self.add_custom_message_simple(channel_id, msg_type, message_data)
            
            response = f"✅ Custom {self.message_types.get(msg_type, msg_type)} message stored!\n\n"
            response += f"• Media: {len(media_items)} items\n"
            response += f"• Text: {len(message_data['text'])} characters\n"
            response += f"• Send Order: {message_data['send_order']}"
            
            await message.reply_text(response)
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_event_media:') and (message.photo or message.video or message.document or message.animation or message.sticker):
            parts = state.split(':')
            channel_id = parts[1]
            event_type = parts[2]
            
            if message.photo:
                media_item = {
                    'type': 'photo',
                    'file_id': message.photo[-1].file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.video:
                media_item = {
                    'type': 'video',
                    'file_id': message.video.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.animation:
                media_item = {
                    'type': 'animation',
                    'file_id': message.animation.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.sticker:
                media_item = {
                    'type': 'sticker',
                    'file_id': message.sticker.file_id,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            elif message.document:
                file_name = message.document.file_name.lower() if message.document.file_name else ""
                mime_type = message.document.mime_type.lower() if message.document.mime_type else ""
                detected_type, actual_type = self.detect_media_type_from_file(file_name, mime_type)
                media_item = {
                    'type': actual_type,
                    'file_id': message.document.file_id,
                    'file_name': file_name,
                    'source_chat_id': message.chat_id,
                    'source_message_id': message.message_id
                }
            else:
                await message.reply_text("❌ Unsupported file type!")
                return
            
            if media_item:
                count = self.add_event_media(channel_id, event_type, media_item)
                file_type = media_item.get('type', 'file')
                await message.reply_text(
                    f"✅ {self.message_types.get(event_type, event_type)} {file_type.upper()} added!\n"
                    f"Total: {count} files\n\n"
                    f"Send more files or type /done to finish."
                )
                
        elif state.startswith('awaiting_event_media:') and text == '/done':
            parts = state.split(':')
            channel_id = parts[1]
            event_type = parts[2]
            media_list = self.get_event_media(channel_id, event_type)
            await message.reply_text(f"✅ Finished adding {self.message_types.get(event_type, event_type)} media!\nTotal media: {len(media_list)}")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_register_link:') and text:
            channel_id = state.split(':', 1)[1]
            self.update_channel_config(channel_id, {'register_link': text})
            await message.reply_text(f"✅ Register link updated for {channel_id}!")
            del self.user_state[chat_id]
            
        elif state.startswith('awaiting_promo_text:') and text:
            channel_id = state.split(':', 1)[1]
            converted_text = self.auto_detect_and_convert_message(text)
            self.update_channel_config(channel_id, {'promotional_text': converted_text})
            await message.reply_text(f"✅ Promotional text updated for {channel_id}!")
            del self.user_state[chat_id]

    def get_message_type_keyboard(self, channel_id):
        buttons = []
        events = list(self.message_types.items())
        for i in range(0, len(events), 2):
            key1, name1 = events[i]
            if i+1 < len(events):
                key2, name2 = events[i+1]
                row = [
                    InlineKeyboardButton(name1, callback_data=f"add_custom_message:{channel_id}:{key1}"),
                    InlineKeyboardButton(name2, callback_data=f"add_custom_message:{channel_id}:{key2}")
                ]
            else:
                row = [InlineKeyboardButton(name1, callback_data=f"add_custom_message:{channel_id}:{key1}")]
            buttons.append(row)
        buttons.append([InlineKeyboardButton("🔙 Cancel", callback_data=f"custom_messages_channel:{channel_id}")])
        return InlineKeyboardMarkup(buttons)

    def detect_media_type_from_file(self, file_name, mime_type=None):
        if not file_name and not mime_type:
            return 'document', 'document'
        
        file_name = str(file_name).lower() if file_name else ''
        mime_type = str(mime_type).lower() if mime_type else ''
        
        if file_name.endswith('.webp') or file_name.endswith('.tgs') or mime_type in ['image/webp', 'application/x-tgsticker']:
            return 'sticker', 'sticker'
        
        video_extensions = ['.mp4', '.mkv', '.mov', '.webm', '.avi']
        if any(file_name.endswith(ext) for ext in video_extensions) or mime_type.startswith('video/'):
            return 'video', 'video'
        
        image_extensions = ['.jpg', '.jpeg', '.png', '.bmp']
        if any(file_name.endswith(ext) for ext in image_extensions) or mime_type.startswith('image/'):
            return 'photo', 'photo'
        
        if file_name.endswith('.gif') or mime_type == 'image/gif':
            return 'animation', 'animation'
        
        return 'document', 'document'

    # ============= KEYBOARD METHODS =============
    
    def get_keyboard(self, keyboard_type, channel_id=None, message_index=None, event_type=None):
        main_menu = [
            [InlineKeyboardButton("📊 Stats & AI", callback_data="stats"), 
             InlineKeyboardButton("⚙️ Channel Settings", callback_data="select_channel_config")],
            [InlineKeyboardButton("⏯️ Prediction Control", callback_data="prediction_control"), 
             InlineKeyboardButton("➕ Add Channel", callback_data="add_channel")],
            [InlineKeyboardButton("🗑️ Remove Channel", callback_data="remove_channel"), 
             InlineKeyboardButton("⏰ Schedule Setup", callback_data="schedule_menu")],
            [InlineKeyboardButton("🎯 Custom Messages", callback_data="custom_messages_menu"), 
             InlineKeyboardButton("📝 Event Media", callback_data="event_media_menu")],
            [InlineKeyboardButton("🤖 AI Management", callback_data="ai_management"),
             InlineKeyboardButton("📝 Templates", callback_data="templates_main_menu")],
            [InlineKeyboardButton("🔄 Advanced", callback_data="advanced"),
             InlineKeyboardButton("📢 Broadcast All", callback_data="broadcast_all")]
        ]
        
        if keyboard_type == 'schedule_menu':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📋 Select Channel", callback_data="select_channel_schedule")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'select_channel_schedule':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="schedule_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"channel_schedule:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"channel_schedule:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="schedule_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'channel_schedule' and channel_id:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("➕ Add Schedule Slot", callback_data=f"add_schedule_slot:{channel_id}")],
                [InlineKeyboardButton("❌ Remove Slot", callback_data=f"remove_schedule_slot:{channel_id}")],
                [InlineKeyboardButton("🗑️ Clear All", callback_data=f"clear_schedule:{channel_id}")],
                [InlineKeyboardButton("🔙 Back", callback_data="select_channel_schedule")]
            ])
        
        if keyboard_type == 'templates_main_menu':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📄 All Templates", callback_data="edit_all_templates"),
                 InlineKeyboardButton("📊 By Channel", callback_data="select_channel_templates")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'edit_all_templates':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🌅 Good Morning", callback_data="edit_template:all:good_morning"),
                 InlineKeyboardButton("🌙 Good Night", callback_data="edit_template:all:good_night")],
                [InlineKeyboardButton("🎯 Single Prediction", callback_data="edit_template:all:single_prediction")],
                [InlineKeyboardButton("🔙 Back", callback_data="templates_main_menu")]
            ])
        
        if keyboard_type == 'ai_management':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📈 AI Statistics", callback_data="ai_stats"),
                 InlineKeyboardButton("🔍 View Patterns", callback_data="view_patterns")],
                [InlineKeyboardButton("🔄 Retrain AI", callback_data="retrain_ai"),
                 InlineKeyboardButton("🧹 Clear AI Data", callback_data="clear_ai_data")],
                [InlineKeyboardButton("🎯 Pattern Analysis", callback_data="pattern_analysis")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'break_duration_menu':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("⏱️ Set Break Duration", callback_data="set_break_duration")],
                [InlineKeyboardButton(f"📊 Current: {self.custom_break_duration} min", callback_data="noop")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'event_media_menu':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📋 Select Channel", callback_data="select_channel_event_media")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'custom_messages_menu':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📋 Select Channel", callback_data="select_channel_custom_messages")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'select_channel_templates':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="templates_main_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"channel_templates:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"channel_templates:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="templates_main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'channel_templates' and channel_id:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🌅 Good Morning", callback_data=f"edit_template:{channel_id}:good_morning"),
                 InlineKeyboardButton("🌙 Good Night", callback_data=f"edit_template:{channel_id}:good_night")],
                [InlineKeyboardButton("🎯 Single Prediction", callback_data=f"edit_template:{channel_id}:single_prediction")],
                [InlineKeyboardButton("🔙 Back", callback_data="select_channel_templates")]
            ])
        
        if keyboard_type == 'select_channel_event_media':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="event_media_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"event_media_channel:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"event_media_channel:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="event_media_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'select_channel_custom_messages':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="custom_messages_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"custom_messages_channel:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"custom_messages_channel:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="custom_messages_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'custom_messages_channel' and channel_id:
            custom_menu = []
            events = list(self.message_types.items())
            for i in range(0, len(events), 2):
                key1, name1 = events[i]
                count1 = len(self.get_custom_messages(channel_id, key1))
                if i+1 < len(events):
                    key2, name2 = events[i+1]
                    count2 = len(self.get_custom_messages(channel_id, key2))
                    row = [
                        InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"custom_messages_type:{channel_id}:{key1}"),
                        InlineKeyboardButton(f"{name2} ({count2})", callback_data=f"custom_messages_type:{channel_id}:{key2}")
                    ]
                else:
                    row = [InlineKeyboardButton(f"{name1} ({count1})", callback_data=f"custom_messages_type:{channel_id}:{key1}")]
                custom_menu.append(row)
            custom_menu.append([InlineKeyboardButton("➕ Add Message", callback_data=f"add_custom_message:{channel_id}")])
            custom_menu.append([InlineKeyboardButton("🔙 Back", callback_data="select_channel_custom_messages")])
            return InlineKeyboardMarkup(custom_menu)
        
        if keyboard_type == 'custom_messages_type' and channel_id and event_type:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton(f"➕ Add {self.message_types.get(event_type, event_type)} Message", callback_data=f"add_custom_message:{channel_id}:{event_type}")],
                [InlineKeyboardButton(f"👁️ View All", callback_data=f"view_custom_messages:{channel_id}:{event_type}")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"custom_messages_channel:{channel_id}")]
            ])
        
        if keyboard_type == 'edit_custom_message' and channel_id and event_type and message_index is not None:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("👁️ Preview", callback_data=f"preview_custom:{channel_id}:{event_type}:{message_index}"),
                 InlineKeyboardButton("🚀 Send Now", callback_data=f"test_send_custom:{channel_id}:{event_type}:{message_index}")],
                [InlineKeyboardButton("🔄 Change Send Order", callback_data=f"change_custom_order:{channel_id}:{event_type}:{message_index}"),
                 InlineKeyboardButton("🗑️ Delete", callback_data=f"delete_custom_message:{channel_id}:{event_type}:{message_index}")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"view_custom_messages:{channel_id}:{event_type}")]
            ])
        
        if keyboard_type == 'send_order_menu' and channel_id and event_type and message_index is not None:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("📝 Text First", callback_data=f"set_custom_order:{channel_id}:{event_type}:{message_index}:text_first"),
                 InlineKeyboardButton("🖼️ Media First", callback_data=f"set_custom_order:{channel_id}:{event_type}:{message_index}:media_first")],
                [InlineKeyboardButton("🎯 Combined", callback_data=f"set_custom_order:{channel_id}:{event_type}:{message_index}:combined")],
                [InlineKeyboardButton("🔙 Back", callback_data=f"edit_custom_message:{channel_id}:{event_type}:{message_index}")]
            ])
        
        if keyboard_type == 'prediction_control':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                channel1 = self.active_channels[i]
                status1 = self.is_channel_prediction_active(channel1)
                row.append(InlineKeyboardButton(f"{'🟢' if status1 else '⏸️'} {channel1}", callback_data=f"toggle_channel_prediction:{channel1}"))
                if i+1 < len(self.active_channels):
                    channel2 = self.active_channels[i+1]
                    status2 = self.is_channel_prediction_active(channel2)
                    row.append(InlineKeyboardButton(f"{'🟢' if status2 else '⏸️'} {channel2}", callback_data=f"toggle_channel_prediction:{channel2}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🟢 Start All", callback_data="start_all_predictions"),
                           InlineKeyboardButton("⏸️ Pause All", callback_data="pause_all_predictions")])
            buttons.append([InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'channel_config' and channel_id:
            channel_status = self.is_channel_prediction_active(channel_id)
            status_text = "⏸️ Pause Predictions" if channel_status else "▶️ Start Predictions"
            
            return InlineKeyboardMarkup([
                [InlineKeyboardButton(status_text, callback_data=f"toggle_single_channel_prediction:{channel_id}")],
                [InlineKeyboardButton("⏰ Schedule Setup", callback_data=f"channel_schedule:{channel_id}"),
                 InlineKeyboardButton("🔗 Links Setup", callback_data=f"links_setup:{channel_id}")],
                [InlineKeyboardButton("📝 Templates", callback_data=f"channel_templates:{channel_id}"),
                 InlineKeyboardButton("📝 Event Media", callback_data=f"event_media_channel:{channel_id}")],
                [InlineKeyboardButton("🎯 Custom Messages", callback_data=f"custom_messages_channel:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'links_setup' and channel_id:
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("✏️ Change Register Link", callback_data=f"change_register_link:{channel_id}"),
                 InlineKeyboardButton("📢 Change Promo Text", callback_data=f"change_promo_text:{channel_id}")],
                [InlineKeyboardButton("🔙 Back to Channel", callback_data=f"channel_config:{channel_id}")]
            ])
        
        if keyboard_type == 'advanced':
            return InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 Reset Session", callback_data="reset_table"),
                 InlineKeyboardButton("🔄 Restart Bot", callback_data="restart_bot")],
                [InlineKeyboardButton("🔍 Resolve Peers", callback_data="resolve_peers")],
                [InlineKeyboardButton("🔙 Back to Main", callback_data="main_menu")]
            ])
        
        if keyboard_type == 'select_channel':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"📢 {self.active_channels[i]}", callback_data=f"channel_config:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"📢 {self.active_channels[i+1]}", callback_data=f"channel_config:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        if keyboard_type == 'remove_channel':
            if not self.active_channels:
                return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Back", callback_data="main_menu")]])
            buttons = []
            for i in range(0, len(self.active_channels), 2):
                row = []
                row.append(InlineKeyboardButton(f"❌ {self.active_channels[i]}", callback_data=f"remove_channel_confirm:{self.active_channels[i]}"))
                if i+1 < len(self.active_channels):
                    row.append(InlineKeyboardButton(f"❌ {self.active_channels[i+1]}", callback_data=f"remove_channel_confirm:{self.active_channels[i+1]}"))
                buttons.append(row)
            buttons.append([InlineKeyboardButton("🔙 Back", callback_data="main_menu")])
            return InlineKeyboardMarkup(buttons)
        
        return InlineKeyboardMarkup(main_menu)

    # ============= MAIN LOOP =============
    
    async def main_loop(self, context):
        logging.info("🚀 Bot started - REAL AI PATTERN RECOGNITION")
        logging.info("⏰ Per-channel custom schedules supported")
        logging.info("🌅 Morning Message: 5:00 AM")
        logging.info("🌙 Night Message: 12:00 AM")
        logging.info("📢 Session Start: 5 minutes before each session")
        logging.info("⏸️ Break Message: At end of each session")
        
        if self.use_user_account:
            success = await self.initialize_user_client()
            if success:
                logging.info("✅ User account ready - Premium emojis available")
            else:
                logging.warning("⚠️ Using regular emojis")
        
        # Track last sent messages per channel
        last_session_start = {}
        last_break = {}
        
        while True:
            try:
                ist_now = self.get_ist_now()
                current_hour = ist_now.hour
                current_minute = ist_now.minute
                current_time_minutes = current_hour * 60 + current_minute
                
                # Morning message at 5:00 AM (global)
                if current_hour == self.morning_message_hour and current_minute == self.morning_message_minute:
                    if not self.morning_message_sent:
                        await self.send_good_morning_message(context)
                        self.morning_message_sent = True
                        self.night_message_sent = False
                        last_session_start.clear()
                        last_break.clear()
                
                if current_hour == self.morning_message_hour and current_minute > self.morning_message_minute:
                    self.morning_message_sent = False
                
                # Night message at 12:00 AM (global)
                if current_hour == self.night_message_hour and current_minute == self.night_message_minute:
                    if not self.night_message_sent:
                        await self.send_good_night_message(context)
                        self.night_message_sent = True
                        self.morning_message_sent = False
                
                if current_hour == self.night_message_hour and current_minute > self.night_message_minute:
                    self.night_message_sent = False
                
                # Process each channel independently
                for channel in self.active_channels:
                    if not self.is_channel_prediction_active(channel):
                        continue
                    
                    # Get channel-specific schedule info
                    is_active, session_start, session_end, next_session, minutes_until, current_slot = self.get_current_session_info_for_channel(channel)
                    
                    if is_active and session_start and session_end:
                        # Check for session start (5 minutes before)
                        # Parse session start time
                        try:
                            start_hour, start_min = 0, 0
                            if current_slot:
                                start_str = current_slot.split('-')[0]
                                start_hour, start_min = map(int, start_str.split(':'))
                            else:
                                start_hour = current_hour
                                start_min = 0
                            
                            start_time = start_hour * 60 + start_min
                            current_minutes = current_hour * 60 + current_minute
                            
                            # Send session start at :55 (5 min before)
                            if start_min > 0 and current_minutes == start_time - 5:
                                session_key = self.get_session_key(channel, f"{start_hour}:{start_min}")
                                if last_session_start.get(channel) != session_key:
                                    await self.send_session_start_message(context, channel, f"{session_start}-{session_end}")
                                    last_session_start[channel] = session_key
                            
                            # Send break at session end
                            end_hour, end_min = 0, 0
                            if current_slot:
                                end_str = current_slot.split('-')[1]
                                end_hour, end_min = map(int, end_str.split(':'))
                            else:
                                end_hour = current_hour
                                end_min = self.prediction_active_minutes
                            
                            end_time = end_hour * 60 + end_min
                            if current_minutes == end_time:
                                session_key = self.get_session_key(channel, f"{end_hour}:{end_min}")
                                if last_break.get(channel) != session_key:
                                    next_start = None
                                    if current_slot:
                                        # Find next slot
                                        slots = self.get_channel_schedule_info(channel)
                                        if slots:
                                            slot_index = slots.index(current_slot) if current_slot in slots else -1
                                            if slot_index != -1 and slot_index + 1 < len(slots):
                                                next_slot = slots[slot_index + 1]
                                                next_start_str = next_slot.split('-')[0]
                                                next_start = self.format_time_str_12h(next_start_str)
                                    else:
                                        next_hour = current_hour + 1 if current_hour < 23 else 6
                                        next_start = self.format_time_12h(next_hour, 0)
                                    
                                    if next_start:
                                        await self.send_break_message_for_channel(context, channel, f"{session_start}-{session_end}", next_start)
                                    else:
                                        await self.send_break_message_for_channel(context, channel, f"{session_start}-{session_end}", "Next Session")
                                    last_break[channel] = session_key
                        except Exception as e:
                            logging.error(f"Schedule processing error for {channel}: {e}")
                
                # Process predictions (global, but only send to active channels)
                # Check if any channel is active for predictions
                any_active = False
                for channel in self.active_channels:
                    if self.is_channel_prediction_active(channel) and self.is_channel_active(channel):
                        any_active = True
                        break
                
                if any_active:
                    data = await self.fetch_live_data()
                    if data:
                        if self.waiting_for_result:
                            await self.check_result_and_send_next(context, data)
                        else:
                            await self.send_first_prediction(context, data)
                
                if self.ai_total_predictions % 25 == 0 and self.ai_total_predictions > 0:
                    self.save_ai_model()
                
                await asyncio.sleep(10)
                
            except Exception as e:
                logging.error(f"❌ Loop error: {e}")
                await asyncio.sleep(30)

    async def shutdown(self):
        if self.user_client_keepalive_task:
            self.user_client_keepalive_task.cancel()
            try:
                await self.user_client_keepalive_task
            except:
                pass
        if self.user_app and self.use_user_account:
            try:
                await self.user_app.stop()
                self.user_client_connected = False
                logging.info("✅ User client stopped")
            except:
                pass

    def run(self):
        class _BotCtx:
            def __init__(self, bot, bot_data):
                self.bot = bot
                self.bot_data = bot_data

        async def _post_init(application):
            _ctx = _BotCtx(application.bot, application.bot_data)
            application.bot_data["main_loop_task"] = asyncio.create_task(self.main_loop(_ctx))

        async def _post_shutdown(application):
            task = application.bot_data.get("main_loop_task")
            if task:
                task.cancel()
                try:
                    await task
                except asyncio.CancelledError:
                    pass
                except Exception:
                    pass
            await self.shutdown()

        application = Application.builder().token(self.bot_token).concurrent_updates(True).connect_timeout(30).read_timeout(30).write_timeout(30).pool_timeout(30).post_init(_post_init).post_shutdown(_post_shutdown).build()
        
        application.add_handler(CommandHandler(["start", "admin"], self.start))
        application.add_handler(CallbackQueryHandler(self.handle_callback))
        application.add_handler(MessageHandler(filters.ALL, self.handle_message))
        
        logging.info("🚀 WinGo Bot Starting...")
        logging.info("🎯 REAL AI PATTERN RECOGNITION SYSTEM")
        logging.info("⏰ Per-channel custom schedules supported")
        logging.info("🌅 Morning Message: 5:00 AM")
        logging.info("🌙 Night Message: 12:00 AM")
        logging.info("📢 Session Start: Sent 5 min before each session")
        logging.info("⏸️ Break Message: Sent at session end")
        
        application.run_polling()


if __name__ == "__main__":
    BOT_TOKEN = "8643497947:AAFJaNMgyYtDCm4Zyacp_-wF5wqyP0kdk1M"
    
    API_ID = 22748653
    API_HASH = "29bba513726e776d0b5fd55dfa893c5a"
    PHONE = "+919934755281"
    
    bot = WinGoBotEnhanced(BOT_TOKEN, api_id=API_ID, api_hash=API_HASH, phone=PHONE)
    bot.run()